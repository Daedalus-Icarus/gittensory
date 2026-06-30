// Static analysis + complexity analyzer (#1477). Scans the ADDED lines of each changed source file for common
// static-defect patterns (eval, debugger, empty-catch, loose equality, console in production code, floating
// promises) and estimates cyclomatic complexity per changed function from decision-point counting. Deterministic,
// pure, no external tools or repo checkout needed — works directly on the patch like the other REES analyzers.
//
// The lint rules are a curated subset that catches real defects without type information (the patch alone is
// enough). This is additive + fail-safe: clean code produces no findings; a timeout/abort degrades to [].
// Language detection gates which rules apply (e.g. `var`/`==` checks are JS/TS-specific).
import type {
  EnrichRequest,
  StaticLintFinding,
  ComplexityFinding,
} from "../types.js";

const MAX_LINT_FINDINGS = 25;
const MAX_COMPLEXITY_FINDINGS = 10;
const COMPLEXITY_THRESHOLD = 10; // flag functions with cyclomatic >= this (matches eslint's default)
const MAX_LINE_CHARS = 2000;

// ── Language detection ────────────────────────────────────────────────────────

export type SourceLanguage =
  | "typescript"
  | "javascript"
  | "python"
  | "go"
  | null;

export function detectLanguage(path: string): SourceLanguage {
  if (/\.(?:tsx?|mts|cts)$/.test(path)) return "typescript";
  if (/\.(?:jsx?|mjs|cjs)$/.test(path)) return "javascript";
  if (/\.py$/i.test(path)) return "python";
  if (/\.go$/i.test(path)) return "go";
  return null;
}

// ── Lint rules ────────────────────────────────────────────────────────────────
// Each rule is a flat regex tested against a single added line (after stripping the `+` prefix). The flat
// alternation keeps each linear-time — no nested quantifiers, no backtracking risk on adversarial input.

type LintRule = {
  rule: string;
  severity: StaticLintFinding["severity"];
  message: string;
  re: RegExp;
  languages: Set<SourceLanguage>;
};

const LINT_RULES: LintRule[] = [
  {
    rule: "no-eval",
    severity: "error",
    message:
      "`eval()` allows arbitrary code execution from attacker-controlled input.",
    re: /\beval\s*\(/,
    languages: new Set([
      "typescript",
      "javascript",
      "python",
    ] as SourceLanguage[]),
  },
  {
    rule: "no-debugger",
    severity: "error",
    message: "`debugger` statement left in production code.",
    re: /\bdebugger\b/,
    languages: new Set(["typescript", "javascript"] as SourceLanguage[]),
  },
  {
    rule: "no-console",
    severity: "warning",
    message:
      "`console` call left in production code — remove or route through a logger.",
    re: /\bconsole\s*\.\s*(?:log|debug|info|warn|error|trace|dir|table)\s*\(/,
    languages: new Set(["typescript", "javascript"] as SourceLanguage[]),
  },
  {
    rule: "no-empty-catch",
    severity: "warning",
    message: "Empty catch block silently swallows errors.",
    re: /\bcatch\s*\([^)]*\)\s*\{\s*\}/,
    languages: new Set(["typescript", "javascript"] as SourceLanguage[]),
  },
  {
    rule: "eqeqeq",
    severity: "warning",
    message:
      "Use strict equality (`===` / `!==`) instead of loose (`==` / `!=`).",
    re: /[^=!<>]==[^=]|[^=!<>]!=[^=]/,
    languages: new Set(["typescript", "javascript"] as SourceLanguage[]),
  },
  {
    rule: "no-unawaited-call",
    severity: "warning",
    message:
      "Standalone call expression — if this returns a Promise, errors are silently lost; add `await` or chain `.catch`.",
    re: /(?:^|[{(;,])\s*(?!.*\bawait\b)(?!.*\breturn\b)[A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)*\([^)]*\)\s*(?:;(?:\s|$)|$)/,
    languages: new Set(["typescript", "javascript"] as SourceLanguage[]),
  },
  {
    rule: "no-var",
    severity: "warning",
    message: "Use `let` or `const` instead of `var`.",
    re: /\bvar\s+/,
    languages: new Set(["typescript", "javascript"] as SourceLanguage[]),
  },
  {
    rule: "no-bare-except",
    severity: "warning",
    message:
      "Bare `except:` catches all exceptions including SystemExit/KeyboardInterrupt — catch specific types.",
    re: /\bexcept\s*:/,
    languages: new Set(["python"] as SourceLanguage[]),
  },
];

function* patchLines(patch: string): Generator<string> {
  let start = 0;
  for (let i = 0; i <= patch.length; i++) {
    if (i === patch.length || patch[i] === "\n") {
      yield patch.slice(start, i);
      start = i + 1;
    }
  }
}

type ScanLimits = {
  maxFindings?: number;
  signal?: AbortSignal;
};

/** Scan one file's added lines for static-defect patterns. Pure + deterministic. */
export function scanPatchForStaticLint(
  path: string,
  patch: string,
  limits: ScanLimits = {},
): StaticLintFinding[] {
  const maxFindings = limits.maxFindings ?? MAX_LINT_FINDINGS;
  if (maxFindings <= 0) return [];
  const lang = detectLanguage(path);
  if (!lang) return [];
  const applicableRules = LINT_RULES.filter((r) => r.languages.has(lang));
  if (applicableRules.length === 0) return [];

  const findings: StaticLintFinding[] = [];
  let newLine = 0;
  for (const line of patchLines(patch)) {
    if (limits.signal?.aborted) throw new Error("analyzer_aborted");
    if (line.startsWith("+++") || line.startsWith("---")) continue;
    const hunk = /^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
    if (hunk) {
      newLine = Number(hunk[1]);
      continue;
    }
    if (line.startsWith("+")) {
      const body = line.slice(1);
      if (body.length <= MAX_LINE_CHARS) {
        for (const rule of applicableRules) {
          if (rule.re.test(body)) {
            findings.push({
              file: path,
              line: newLine,
              rule: rule.rule,
              severity: rule.severity,
              message: rule.message,
            });
            if (findings.length >= maxFindings) return findings;
            break; // one finding per line — the first matching rule
          }
        }
      }
      newLine++;
    } else if (!line.startsWith("-")) {
      newLine++;
    }
  }
  return findings;
}

// ── Cyclomatic complexity ─────────────────────────────────────────────────────

const DECISION_RE = /\b(?:if|else\s+if|for|while|case|catch)\b|\?|&&|\|\|/g;
const FUNCTION_DECL_RE =
  /(?:function\s+([A-Za-z_$][\w$]*)|(?:const|let|var)\s+([A-Za-z_$][\w$]*)\s*=\s*(?:async\s*)?\([^)]*\)\s*=>|def\s+([A-Za-z_][\w]*)|func\s+([A-Za-z_][\w]*))/;

/** Count decision points in a code line (the cyclomatic-complexity increment). Pure. */
export function countDecisions(line: string): number {
  const matches = line.match(DECISION_RE);
  return matches ? matches.length : 0;
}

/** Extract the function name from a declaration line, or null if the line isn't a function declaration. Pure. */
export function extractFunctionName(line: string): string | null {
  const m = FUNCTION_DECL_RE.exec(line);
  if (!m) return null;
  return m[1] ?? m[2] ?? m[3] ?? m[4] ?? null;
}

interface FunctionAccumulator {
  name: string;
  cyclomatic: number;
  churn: number;
  /** The brace depth at the function's opening brace — the function ends when depth returns to this. */
  baseDepth: number;
}

/** Scan one file's added lines for high-complexity functions. Pure + deterministic.
 *  Detects function declarations from BOTH added lines AND context lines so that added decision logic
 *  inside an existing unchanged function is correctly counted.
 *  Limited to TypeScript/JavaScript — Go/Python function-end tracking (indentation-based for Python) is a
 *  follow-up; without it, decision points would leak across function boundaries. */
export function scanPatchForComplexity(
  path: string,
  patch: string,
  limits: ScanLimits = {},
): ComplexityFinding[] {
  const maxFindings = limits.maxFindings ?? MAX_COMPLEXITY_FINDINGS;
  if (maxFindings <= 0) return [];
  const lang = detectLanguage(path);
  if (lang !== "typescript" && lang !== "javascript") return [];

  const findings: ComplexityFinding[] = [];
  let current: FunctionAccumulator | null = null;
  let braceDepth = 0;
  let newLine = 0;

  const flush = () => {
    if (current && current.cyclomatic >= COMPLEXITY_THRESHOLD) {
      findings.push({
        file: path,
        function: current.name,
        cyclomatic: current.cyclomatic,
        churn: current.churn,
      });
    }
    current = null;
  };

  for (const line of patchLines(patch)) {
    if (limits.signal?.aborted) throw new Error("analyzer_aborted");
    if (line.startsWith("+++") || line.startsWith("---")) continue;
    const hunk = /^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
    if (hunk) {
      flush();
      braceDepth = 0;
      newLine = Number(hunk[1]);
      continue;
    }
    const isAdded = line.startsWith("+");
    const isRemoved = line.startsWith("-");
    const body = isAdded ? line.slice(1) : isRemoved ? line.slice(1) : line;
    if (body.length > MAX_LINE_CHARS) {
      if (isAdded) newLine++;
      else if (!isRemoved) newLine++;
      continue;
    }

    // Detect a new function declaration from EITHER added lines OR context lines (the blocker fix:
    // a PR that adds `if`/`for`/`&&` inside an existing function whose declaration is just hunk context
    // must still produce a complexity finding for that function).
    const fnName = extractFunctionName(body);
    if (fnName && !isRemoved) {
      flush();
      current = {
        name: fnName,
        cyclomatic: 1,
        churn: 0,
        baseDepth: braceDepth,
      };
    }

    // Track brace depth from ALL lines (added + context) so function-end detection works.
    if (lang === "typescript" || lang === "javascript") {
      for (const ch of body) {
        if (ch === "{") {
          braceDepth++;
        } else if (ch === "}") {
          braceDepth--;
          // A closing brace that returns to or below the function's opening depth ends the function.
          if (current && braceDepth <= current.baseDepth) {
            flush();
          }
        }
      }
    }

    // Accumulate decision points from ADDED lines only (churn is the new code's complexity contribution).
    if (isAdded && current) {
      current.cyclomatic += countDecisions(body);
      current.churn++;
    }

    if (isAdded) newLine++;
    else if (!isRemoved) newLine++;
  }
  flush();

  findings.sort((a, b) => b.cyclomatic - a.cyclomatic);
  return findings.slice(0, maxFindings);
}

// ── Analyzer entrypoints ──────────────────────────────────────────────────────

type ScanOptions = { signal?: AbortSignal };

/** Analyzer entrypoint: scan every changed source file's added lines for static defects. */
export async function scanStaticLint(
  req: EnrichRequest,
  _fetchFn: typeof fetch = fetch,
  options: ScanOptions = {},
): Promise<StaticLintFinding[]> {
  const findings: StaticLintFinding[] = [];
  for (const file of req.files ?? []) {
    if (options.signal?.aborted) throw new Error("analyzer_aborted");
    if (!file.patch) continue;
    const lint = scanPatchForStaticLint(file.path, file.patch, {
      maxFindings: MAX_LINT_FINDINGS - findings.length,
      signal: options.signal,
    });
    findings.push(...lint);
    if (findings.length >= MAX_LINT_FINDINGS) break;
  }
  return findings;
}

/** Analyzer entrypoint: scan every changed source file's added lines for high-complexity functions. */
export async function scanComplexity(
  req: EnrichRequest,
  _fetchFn: typeof fetch = fetch,
  options: ScanOptions = {},
): Promise<ComplexityFinding[]> {
  const findings: ComplexityFinding[] = [];
  for (const file of req.files ?? []) {
    if (options.signal?.aborted) throw new Error("analyzer_aborted");
    if (!file.patch) continue;
    const complexity = scanPatchForComplexity(file.path, file.patch, {
      maxFindings: MAX_COMPLEXITY_FINDINGS - findings.length,
      signal: options.signal,
    });
    findings.push(...complexity);
  }
  return findings;
}
