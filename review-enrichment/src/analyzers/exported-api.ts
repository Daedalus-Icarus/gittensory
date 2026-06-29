// Exported-API breaking-change detector (#1510). Compares the currently-published npm package's declaration
// entrypoints to the post-PR declaration surface reconstructed from the diff. It flags semver-major breaks that
// ship as patch/minor work: removed exported entrypoints, removed exported symbols, and changed exported signatures.
// Fail-safe by construction: when the package name is unknown, the registry/tarball cannot be fetched, or the head
// surface cannot be reconstructed from the diff, this returns [] rather than guessing.
import { gunzipSync } from "node:zlib";
import { posix as pathPosix } from "node:path";
import type { EnrichRequest, ExportedApiFinding } from "../types.js";

const NPM_PACKAGE_RE =
  /^(?:@[a-z0-9][a-z0-9._-]*\/[a-z0-9][a-z0-9._-]*|[a-z0-9][a-z0-9._-]*)$/;
const MAX_CANDIDATE_PACKAGES = 5;
const MAX_FINDINGS = 20;
const MAX_TARBALL_BYTES = 8 * 1024 * 1024;
const MAX_EXTRACTED_FILES = 200;
const MAX_TEXT_FILE_BYTES = 256 * 1024;

type PackageCandidate = {
  root: string;
  name: string;
};

type ExportSurface = Map<string, string>;

type SurfaceResult = {
  exports: ExportSurface;
  complete: boolean;
};

type PackageMetadata = {
  publishedVersion: string;
  files: Map<string, string>;
  packageJson: string;
};

const DECLARATION_EXTENSIONS = [".d.ts", ".d.mts", ".d.cts"] as const;

function isDeclarationFile(path: string): boolean {
  return DECLARATION_EXTENSIONS.some((ext) => path.endsWith(ext));
}

function normalizeRelativePath(value: string): string | null {
  const normalized = pathPosix.normalize(value.replace(/^\.\/+/, ""));
  if (!normalized || normalized.startsWith("../") || normalized === "..") {
    return null;
  }
  return normalized;
}

function stripComments(source: string): string {
  let out = "";
  let i = 0;
  let quote: "'" | '"' | "`" | null = null;
  while (i < source.length) {
    const char = source[i]!;
    const next = source[i + 1];
    if (quote) {
      out += char;
      if (char === "\\" && next) {
        out += next;
        i += 2;
        continue;
      }
      if (char === quote) quote = null;
      i += 1;
      continue;
    }
    if (char === "'" || char === '"' || char === "`") {
      quote = char;
      out += char;
      i += 1;
      continue;
    }
    if (char === "/" && next === "/") {
      while (i < source.length && source[i] !== "\n") i += 1;
      continue;
    }
    if (char === "/" && next === "*") {
      i += 2;
      while (i + 1 < source.length && !(source[i] === "*" && source[i + 1] === "/")) {
        i += 1;
      }
      i = Math.min(source.length, i + 2);
      continue;
    }
    out += char;
    i += 1;
  }
  return out;
}

function nextNonWhitespace(source: string, start: number): number {
  for (let i = start; i < source.length; i += 1) {
    if (!/\s/.test(source[i]!)) return i;
  }
  return -1;
}

function extractExportStatements(source: string): string[] {
  const cleaned = stripComments(source);
  const statements: string[] = [];
  let quote: "'" | '"' | "`" | null = null;
  let braceDepth = 0;
  let parenDepth = 0;
  let bracketDepth = 0;
  let start = -1;
  for (let i = 0; i < cleaned.length; i += 1) {
    const char = cleaned[i]!;
    const next = cleaned[i + 1];
    if (quote) {
      if (char === "\\" && next) {
        i += 1;
        continue;
      }
      if (char === quote) quote = null;
      continue;
    }
    if (char === "'" || char === '"' || char === "`") {
      quote = char;
      continue;
    }
    if (char === "{") braceDepth += 1;
    else if (char === "}") braceDepth = Math.max(0, braceDepth - 1);
    else if (char === "(") parenDepth += 1;
    else if (char === ")") parenDepth = Math.max(0, parenDepth - 1);
    else if (char === "[") bracketDepth += 1;
    else if (char === "]") bracketDepth = Math.max(0, bracketDepth - 1);

    if (
      start === -1 &&
      braceDepth === 0 &&
      parenDepth === 0 &&
      bracketDepth === 0 &&
      cleaned.startsWith("export", i) &&
      (i === 0 || /[\s;{}]/.test(cleaned[i - 1]!))
    ) {
      start = i;
    }
    if (start === -1) continue;

    const atTopLevel =
      braceDepth === 0 && parenDepth === 0 && bracketDepth === 0;
    if (atTopLevel && char === ";") {
      statements.push(cleaned.slice(start, i + 1).trim());
      start = -1;
      continue;
    }
    if (atTopLevel && char === "}") {
      const nextIndex = nextNonWhitespace(cleaned, i + 1);
      if (nextIndex === -1 || cleaned.startsWith("export", nextIndex)) {
        statements.push(cleaned.slice(start, i + 1).trim());
        start = -1;
      }
    }
  }
  if (start !== -1) statements.push(cleaned.slice(start).trim());
  return statements.filter(Boolean);
}

function normalizeSignature(signature: string): string {
  return signature
    .replace(/\s+/g, " ")
    .replace(/\s*([{}();,:<>=\[\]|&?])\s*/g, "$1")
    .replace(/\bexport\s+/g, "")
    .replace(/\bdeclare\s+/g, "")
    .trim();
}

function summarizeSignature(signature: string): string {
  const normalized = normalizeSignature(signature);
  return normalized.length > 140
    ? `${normalized.slice(0, 137)}...`
    : normalized;
}

function parseExportSpecifiers(body: string): Array<{ imported: string; exported: string }> {
  const specs: Array<{ imported: string; exported: string }> = [];
  for (const rawPart of body.split(",")) {
    const part = rawPart.trim();
    if (!part) continue;
    const match = /^([A-Za-z_$][\w$]*)(?:\s+as\s+([A-Za-z_$][\w$]*))?$/.exec(part);
    if (!match) continue;
    specs.push({
      imported: match[1]!,
      exported: match[2] ?? match[1]!,
    });
  }
  return specs;
}

function parseDirectExport(
  statement: string,
): { symbol: string; signature: string } | null {
  const directMatchers: Array<RegExp> = [
    /^export\s+default\b/i,
    /^export\s*=\s*/i,
    /^export\s+(?:declare\s+)?(?:async\s+)?function\s+([A-Za-z_$][\w$]*)/i,
    /^export\s+(?:declare\s+)?(?:const|let|var)\s+([A-Za-z_$][\w$]*)/i,
    /^export\s+(?:declare\s+)?(?:abstract\s+)?class\s+([A-Za-z_$][\w$]*)/i,
    /^export\s+interface\s+([A-Za-z_$][\w$]*)/i,
    /^export\s+type\s+([A-Za-z_$][\w$]*)/i,
    /^export\s+(?:declare\s+)?enum\s+([A-Za-z_$][\w$]*)/i,
    /^export\s+(?:declare\s+)?namespace\s+([A-Za-z_$][\w$]*)/i,
  ];
  for (const matcher of directMatchers) {
    const match = matcher.exec(statement);
    if (!match) continue;
    return {
      symbol: match[1] ?? "default",
      signature: normalizeSignature(statement),
    };
  }
  return null;
}

function declarationCandidates(basePath: string, specifier: string): string[] {
  const baseDir = pathPosix.dirname(basePath);
  const resolved = normalizeRelativePath(pathPosix.join(baseDir, specifier));
  if (!resolved) return [];
  const candidates = new Set<string>();
  candidates.add(resolved);
  if (isDeclarationFile(resolved)) return [...candidates];
  if (/\.(?:mjs|mts)$/i.test(resolved)) candidates.add(resolved.replace(/\.(?:mjs|mts)$/i, ".d.mts"));
  if (/\.(?:cjs|cts)$/i.test(resolved)) candidates.add(resolved.replace(/\.(?:cjs|cts)$/i, ".d.cts"));
  if (/\.(?:js|ts)$/i.test(resolved)) candidates.add(resolved.replace(/\.(?:js|ts)$/i, ".d.ts"));
  for (const ext of DECLARATION_EXTENSIONS) candidates.add(`${resolved}${ext}`);
  for (const ext of DECLARATION_EXTENSIONS) {
    candidates.add(pathPosix.join(resolved, `index${ext}`));
  }
  return [...candidates];
}

function resolveDeclarationPath(
  basePath: string,
  specifier: string,
  files: Map<string, string>,
): string | null {
  if (!specifier.startsWith(".")) return null;
  for (const candidate of declarationCandidates(basePath, specifier)) {
    if (files.has(candidate)) return candidate;
  }
  return null;
}

function collectExportSurface(
  filePath: string,
  files: Map<string, string>,
  cache = new Map<string, SurfaceResult>(),
  stack = new Set<string>(),
): SurfaceResult {
  const cached = cache.get(filePath);
  if (cached) return cached;
  if (stack.has(filePath)) return { exports: new Map(), complete: false };
  const source = files.get(filePath);
  if (typeof source !== "string") return { exports: new Map(), complete: false };

  stack.add(filePath);
  const surface: ExportSurface = new Map();
  let complete = true;
  for (const statement of extractExportStatements(source)) {
    const direct = parseDirectExport(statement);
    if (direct) {
      surface.set(direct.symbol, direct.signature);
      continue;
    }

    const namespaceMatch =
      /^export\s+\*\s+as\s+([A-Za-z_$][\w$]*)\s+from\s+["']([^"']+)["'];?$/i.exec(
        statement,
      );
    if (namespaceMatch) {
      surface.set(namespaceMatch[1]!, normalizeSignature(statement));
      continue;
    }

    const exportAllMatch =
      /^export\s+\*\s+from\s+["']([^"']+)["'];?$/i.exec(statement);
    if (exportAllMatch) {
      const targetPath = resolveDeclarationPath(filePath, exportAllMatch[1]!, files);
      if (!targetPath) {
        complete = false;
        continue;
      }
      const target = collectExportSurface(targetPath, files, cache, stack);
      complete = complete && target.complete;
      for (const [symbol, signature] of target.exports) {
        if (symbol !== "default") surface.set(symbol, signature);
      }
      continue;
    }

    const reexportMatch =
      /^export\s+(?:type\s+)?\{([^}]+)\}\s+from\s+["']([^"']+)["'];?$/i.exec(
        statement,
      );
    if (reexportMatch) {
      const targetPath = resolveDeclarationPath(filePath, reexportMatch[2]!, files);
      const target = targetPath
        ? collectExportSurface(targetPath, files, cache, stack)
        : { exports: new Map(), complete: false };
      complete = complete && target.complete;
      for (const spec of parseExportSpecifiers(reexportMatch[1]!)) {
        surface.set(
          spec.exported,
          target.exports.get(spec.imported) ??
            normalizeSignature(
              `export ${spec.exported} from ${reexportMatch[2]}#${spec.imported}`,
            ),
        );
      }
      continue;
    }

    const localReexportMatch =
      /^export\s+(?:type\s+)?\{([^}]+)\};?$/i.exec(statement);
    if (localReexportMatch) {
      for (const spec of parseExportSpecifiers(localReexportMatch[1]!)) {
        surface.set(
          spec.exported,
          normalizeSignature(`export ${spec.exported} = ${spec.imported}`),
        );
      }
    }
  }

  const result = { exports: surface, complete };
  cache.set(filePath, result);
  stack.delete(filePath);
  return result;
}

function extractTypePathFromExport(value: unknown): string | null {
  if (typeof value === "string") return isDeclarationFile(value) ? value : null;
  if (!value || typeof value !== "object") return null;
  const record = value as Record<string, unknown>;
  if (typeof record.types === "string") return record.types;
  for (const key of ["import", "require", "default", "node", "browser"]) {
    const nested = extractTypePathFromExport(record[key]);
    if (nested) return nested;
  }
  for (const nestedValue of Object.values(record)) {
    const nested = extractTypePathFromExport(nestedValue);
    if (nested) return nested;
  }
  return null;
}

export function extractTypeEntrypoints(packageJson: unknown): Map<string, string> {
  const entrypoints = new Map<string, string>();
  if (!packageJson || typeof packageJson !== "object") return entrypoints;
  const record = packageJson as Record<string, unknown>;
  if (record.exports && typeof record.exports === "object") {
    for (const [entry, value] of Object.entries(record.exports)) {
      const typePath = extractTypePathFromExport(value);
      const normalized = typePath ? normalizeRelativePath(typePath) : null;
      if (normalized) entrypoints.set(entry, normalized);
    }
  }
  if (!entrypoints.size) {
    const fallback = [record.types, record.typings].find(
      (value): value is string => typeof value === "string",
    );
    const normalized = fallback ? normalizeRelativePath(fallback) : null;
    if (normalized) entrypoints.set(".", normalized);
  }
  return entrypoints;
}

function readTarPath(buffer: Buffer, start: number, length: number): string {
  return buffer
    .toString("utf8", start, start + length)
    .replace(/\0.*$/, "")
    .trim();
}

function readTarSize(buffer: Buffer, start: number): number {
  const raw = buffer
    .toString("utf8", start, start + 12)
    .replace(/\0.*$/, "")
    .trim();
  return raw ? Number.parseInt(raw, 8) : 0;
}

export function extractTarTextFiles(archive: Uint8Array): Map<string, string> {
  const files = new Map<string, string>();
  let tar: Buffer;
  try {
    tar = gunzipSync(Buffer.from(archive));
  } catch {
    return files;
  }

  for (let offset = 0; offset + 512 <= tar.length; ) {
    const header = tar.subarray(offset, offset + 512);
    if (header.every((byte) => byte === 0)) break;
    const name = readTarPath(tar, offset, 100);
    const prefix = readTarPath(tar, offset + 345, 155);
    const size = readTarSize(tar, offset + 124);
    const typeFlag = tar[offset + 156];
    const fullName = prefix ? `${prefix}/${name}` : name;
    const nextOffset = offset + 512 + Math.ceil(size / 512) * 512;
    offset += 512;
    if (typeFlag !== 0 && typeFlag !== 48) {
      offset = nextOffset;
      continue;
    }
    if (size > MAX_TEXT_FILE_BYTES) {
      offset = nextOffset;
      continue;
    }
    const normalized = fullName.replace(/^package\//, "");
    if (!normalized || (!isDeclarationFile(normalized) && normalized !== "package.json")) {
      offset = nextOffset;
      continue;
    }
    files.set(normalizeRelativePath(normalized) ?? normalized, tar.toString("utf8", offset, offset + size));
    if (files.size >= MAX_EXTRACTED_FILES) break;
    offset = nextOffset;
  }
  return files;
}

export function applyUnifiedPatch(base: string, patch: string): string | null {
  const sourceLines = base === "" ? [] : base.split("\n");
  const patchLines = patch.split("\n");
  const out: string[] = [];
  let sourceIndex = 0;
  let i = 0;

  while (i < patchLines.length) {
    const header = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(
      patchLines[i]!,
    );
    if (!header) {
      i += 1;
      continue;
    }
    const oldStart = Math.max(0, Number(header[1]!) - 1);
    while (sourceIndex < oldStart) {
      out.push(sourceLines[sourceIndex]!);
      sourceIndex += 1;
    }
    i += 1;
    while (i < patchLines.length && !patchLines[i]!.startsWith("@@ ")) {
      const line = patchLines[i]!;
      if (line.startsWith("\\ No newline at end of file")) {
        i += 1;
        continue;
      }
      const prefix = line[0];
      const body = line.slice(1);
      if (prefix === " ") {
        if (sourceLines[sourceIndex] !== body) return null;
        out.push(body);
        sourceIndex += 1;
      } else if (prefix === "-") {
        if (sourceLines[sourceIndex] !== body) return null;
        sourceIndex += 1;
      } else if (prefix === "+") {
        out.push(body);
      } else {
        return null;
      }
      i += 1;
    }
  }
  while (sourceIndex < sourceLines.length) {
    out.push(sourceLines[sourceIndex]!);
    sourceIndex += 1;
  }
  return out.join("\n");
}

export function extractPackageNameFromPatch(patch: string | undefined): string | null {
  if (!patch) return null;
  for (const rawLine of patch.split("\n")) {
    const body = /^[ +\-]/.test(rawLine) ? rawLine.slice(1) : rawLine;
    const match = /^\s*"name"\s*:\s*"([^"]+)"/.exec(body);
    if (match) return match[1]!;
  }
  return null;
}

function findPackageCandidates(
  files: NonNullable<EnrichRequest["files"]>,
): PackageCandidate[] {
  const seen = new Set<string>();
  const candidates: PackageCandidate[] = [];
  for (const file of files) {
    if (candidates.length >= MAX_CANDIDATE_PACKAGES) break;
    if (!file.path.endsWith("package.json") || !file.patch) continue;
    const name = extractPackageNameFromPatch(file.patch);
    if (!name || !NPM_PACKAGE_RE.test(name)) continue;
    const root = file.path === "package.json"
      ? ""
      : file.path.slice(0, -"/package.json".length);
    const key = `${root}\u0000${name}`;
    if (seen.has(key)) continue;
    seen.add(key);
    candidates.push({ root, name });
  }
  return candidates;
}

type ManifestEntrypointOverlay = {
  set: Map<string, string>;
  removed: Set<string>;
};

function countChar(line: string, char: string): number {
  let count = 0;
  for (const value of line) {
    if (value === char) count += 1;
  }
  return count;
}

function visiblePatchLines(
  patch: string,
  side: "base" | "head",
): string[] {
  const lines: string[] = [];
  for (const rawLine of patch.split("\n")) {
    if (
      rawLine.startsWith("@@ ") ||
      rawLine.startsWith("\\ No newline at end of file")
    ) {
      continue;
    }
    if (!rawLine) continue;
    const prefix = rawLine[0];
    if (prefix === " " || (side === "base" ? prefix === "-" : prefix === "+")) {
      lines.push(rawLine.slice(1));
    }
  }
  return lines;
}

function parseManifestEntrypoints(lines: string[]): Map<string, string> {
  const entrypoints = new Map<string, string>();
  let depth = 0;
  let exportsDepth = -1;
  let currentEntrypoint: string | null = null;
  let currentEntrypointDepth = -1;

  for (const rawLine of lines) {
    const line = rawLine.trim();
    const inExports = exportsDepth !== -1 && depth >= exportsDepth;

    if (!inExports) {
      const topLevelTypes =
        /^"(types|typings)"\s*:\s*"([^"]+)"/.exec(line);
      const normalizedTopLevel = topLevelTypes
        ? normalizeRelativePath(topLevelTypes[2]!)
        : null;
      if (normalizedTopLevel) entrypoints.set(".", normalizedTopLevel);
    }

    if (!inExports) {
      const exportsMatch = /^"exports"\s*:\s*\{/.exec(line);
      if (exportsMatch) {
        exportsDepth = depth + 1;
      }
    } else {
      const inlineEntrypoint =
        /^"(\.[^"]*)"\s*:\s*\{\s*"types"\s*:\s*"([^"]+)"/.exec(line);
      const normalizedInline = inlineEntrypoint
        ? normalizeRelativePath(inlineEntrypoint[2]!)
        : null;
      if (inlineEntrypoint && normalizedInline) {
        entrypoints.set(inlineEntrypoint[1]!, normalizedInline);
      } else {
        const objectEntrypoint = /^"(\.[^"]*)"\s*:\s*\{/.exec(line);
        if (objectEntrypoint) {
          currentEntrypoint = objectEntrypoint[1]!;
          currentEntrypointDepth = depth + 1;
        }

        const directEntrypoint =
          /^"(\.[^"]*)"\s*:\s*"([^"]+)"/.exec(line);
        const normalizedDirect = directEntrypoint
          ? normalizeRelativePath(directEntrypoint[2]!)
          : null;
        if (directEntrypoint && normalizedDirect && isDeclarationFile(normalizedDirect)) {
          entrypoints.set(directEntrypoint[1]!, normalizedDirect);
        }

        if (currentEntrypoint) {
          const typesMatch = /^"(types|typings)"\s*:\s*"([^"]+)"/.exec(line);
          const normalizedTypes = typesMatch
            ? normalizeRelativePath(typesMatch[2]!)
            : null;
          if (normalizedTypes) entrypoints.set(currentEntrypoint, normalizedTypes);
        }
      }
    }

    depth += countChar(line, "{");
    depth -= countChar(line, "}");

    if (currentEntrypoint && depth < currentEntrypointDepth) {
      currentEntrypoint = null;
      currentEntrypointDepth = -1;
    }
    if (exportsDepth !== -1 && depth < exportsDepth) {
      exportsDepth = -1;
      currentEntrypoint = null;
      currentEntrypointDepth = -1;
    }
  }

  return entrypoints;
}

function deriveManifestEntrypointOverlay(
  patch: string | undefined,
): ManifestEntrypointOverlay {
  const overlay: ManifestEntrypointOverlay = {
    set: new Map(),
    removed: new Set(),
  };
  if (!patch) return overlay;

  const base = parseManifestEntrypoints(visiblePatchLines(patch, "base"));
  const head = parseManifestEntrypoints(visiblePatchLines(patch, "head"));

  for (const [entrypoint, typePath] of head) overlay.set.set(entrypoint, typePath);
  for (const entrypoint of base.keys()) {
    if (!head.has(entrypoint)) overlay.removed.add(entrypoint);
  }
  return overlay;
}

export function applyManifestEntrypointOverlay(
  publishedEntrypoints: Map<string, string>,
  patch: string | undefined,
): Map<string, string> {
  const next = new Map(publishedEntrypoints);
  const overlay = deriveManifestEntrypointOverlay(patch);
  for (const entrypoint of overlay.removed) next.delete(entrypoint);
  for (const [entrypoint, typePath] of overlay.set) next.set(entrypoint, typePath);
  return next;
}

function relativeToPackageRoot(root: string, filePath: string): string | null {
  if (!root) return normalizeRelativePath(filePath);
  if (filePath === root) return null;
  if (!filePath.startsWith(`${root}/`)) return null;
  return normalizeRelativePath(filePath.slice(root.length + 1));
}

async function fetchPublishedPackage(
  name: string,
  fetchImpl: typeof fetch,
  signal?: AbortSignal,
): Promise<PackageMetadata | null> {
  const metadataResponse = await fetchImpl(
    `https://registry.npmjs.org/${encodeURIComponent(name)}`,
    { signal },
  ).catch(() => null);
  if (!metadataResponse?.ok) return null;
  const metadata = (await metadataResponse.json().catch(() => null)) as
    | {
        "dist-tags"?: { latest?: string };
        versions?: Record<string, { dist?: { tarball?: string } }>;
      }
    | null;
  const publishedVersion = metadata?.["dist-tags"]?.latest;
  const tarballUrl = publishedVersion
    ? metadata?.versions?.[publishedVersion]?.dist?.tarball
    : undefined;
  if (!publishedVersion || !tarballUrl) return null;

  const tarballResponse = await fetchImpl(tarballUrl, { signal }).catch(
    () => null,
  );
  if (!tarballResponse?.ok) return null;
  const tarball = new Uint8Array(await tarballResponse.arrayBuffer());
  if (tarball.byteLength > MAX_TARBALL_BYTES) return null;
  const files = extractTarTextFiles(tarball);
  const packageJson = files.get("package.json");
  if (!packageJson) return null;
  return { publishedVersion, files, packageJson };
}

function reconstructHeadFiles(
  root: string,
  packageFiles: NonNullable<EnrichRequest["files"]>,
  publishedFiles: Map<string, string>,
): Map<string, string> | null {
  const next = new Map(publishedFiles);
  for (const file of packageFiles) {
    const relativePath = relativeToPackageRoot(root, file.path);
    if (!relativePath) continue;

    const previousRelative = file.previousPath
      ? relativeToPackageRoot(root, file.previousPath)
      : null;
    if (
      file.status === "renamed" &&
      previousRelative &&
      previousRelative !== relativePath &&
      next.has(previousRelative)
    ) {
      next.set(relativePath, next.get(previousRelative)!);
      next.delete(previousRelative);
    }
    if (file.status === "removed") {
      next.delete(relativePath);
      continue;
    }
    if (relativePath === "package.json") continue;
    if (!file.patch) continue;
    const base = previousRelative && previousRelative !== relativePath
      ? next.get(relativePath) ?? next.get(previousRelative) ?? ""
      : next.get(relativePath) ?? "";
    const reconstructed = applyUnifiedPatch(base, file.patch);
    if (reconstructed === null) return null;
    next.set(relativePath, reconstructed);
  }
  return next;
}

function compareEntrypoint(
  packageName: string,
  publishedVersion: string,
  entrypoint: string,
  publishedTypePath: string,
  headTypePath: string,
  publishedFiles: Map<string, string>,
  headFiles: Map<string, string>,
): ExportedApiFinding[] {
  const publishedSurface = collectExportSurface(publishedTypePath, publishedFiles);
  const headSurface = collectExportSurface(headTypePath, headFiles);
  if (!publishedSurface.complete || !headSurface.complete) return [];

  const findings: ExportedApiFinding[] = [];
  for (const [symbol, publishedSignature] of publishedSurface.exports) {
    if (findings.length >= MAX_FINDINGS) break;
    const headSignature = headSurface.exports.get(symbol);
    if (!headSignature) {
      findings.push({
        package: packageName,
        publishedVersion,
        entrypoint,
        typePath: publishedTypePath,
        kind: "removed-export",
        symbol,
      });
      continue;
    }
    if (publishedSignature !== headSignature) {
      findings.push({
        package: packageName,
        publishedVersion,
        entrypoint,
        typePath: publishedTypePath,
        kind: "signature-changed",
        symbol,
        before: summarizeSignature(publishedSignature),
        after: summarizeSignature(headSignature),
      });
    }
  }
  return findings;
}

export async function scanExportedApi(
  req: EnrichRequest,
  fetchImpl: typeof fetch = fetch,
  options: { signal?: AbortSignal } = {},
): Promise<ExportedApiFinding[]> {
  const files = req.files ?? [];
  const findings: ExportedApiFinding[] = [];

  for (const candidate of findPackageCandidates(files)) {
    if (options.signal?.aborted || findings.length >= MAX_FINDINGS) break;
    const published = await fetchPublishedPackage(
      candidate.name,
      fetchImpl,
      options.signal,
    );
    if (!published) continue;

    const headFiles = reconstructHeadFiles(
      candidate.root,
      files,
      published.files,
    );
    if (!headFiles) continue;

    const publishedPackageJson = JSON.parse(published.packageJson) as unknown;
    const packageJsonPatch = files.find(
      (file) => file.path === (candidate.root ? `${candidate.root}/package.json` : "package.json"),
    )?.patch;

    const publishedEntrypoints = extractTypeEntrypoints(publishedPackageJson);
    const headEntrypoints = applyManifestEntrypointOverlay(
      publishedEntrypoints,
      packageJsonPatch,
    );
    if (!publishedEntrypoints.size) continue;

    for (const [entrypoint, publishedTypePath] of publishedEntrypoints) {
      if (findings.length >= MAX_FINDINGS) break;
      const headTypePath = headEntrypoints.get(entrypoint);
      if (!headTypePath) {
        findings.push({
          package: candidate.name,
          publishedVersion: published.publishedVersion,
          entrypoint,
          typePath: publishedTypePath,
          kind: "removed-entrypoint",
        });
        continue;
      }
      if (!headFiles.has(headTypePath)) {
        findings.push({
          package: candidate.name,
          publishedVersion: published.publishedVersion,
          entrypoint,
          typePath: publishedTypePath,
          kind: "removed-entrypoint",
        });
        continue;
      }
      for (const finding of compareEntrypoint(
        candidate.name,
        published.publishedVersion,
        entrypoint,
        publishedTypePath,
        headTypePath,
        published.files,
        headFiles,
      )) {
        findings.push(finding);
        if (findings.length >= MAX_FINDINGS) break;
      }
    }
  }

  return findings;
}
