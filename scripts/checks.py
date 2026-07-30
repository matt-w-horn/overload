#!/usr/bin/env python3
"""Prose-side checks for the Overload library. Invoked by the test driver
(`lake exe overloadTest`, stage 6). The proof-token scanner reads source
because Lean never adds an `example` to the environment, so no environment
sweep can see one.

Usage: checks.py <repo-root>
       checks.py --scan FILE...   (proof-token scan; exit 1 on any hit)

Hard failures (exit 1, written to a fresh .verify/DISCREPANCIES.md; a green
run removes the ledger): section-refs, proof-tokens.
"""
import re
import sys
from pathlib import Path


# --- proof-token scanning (shared by the sweep below and `--scan`).
# The environment sweep in AxiomAudit.lean cannot see `example`s: Lean never
# adds them to the environment, so no name-based check reaches them and a
# `sorry` inside one builds green (verified 2026-07-24). This is the backstop
# that holds for every declaration kind. Comments and docstrings are stripped
# first — the tokens appear legitimately in prose (Basic.lean's "Zero
# `sorry`", Deadline's English "admit").
#
# The 2026-07-29 linter campaign (`--wfail` build, mathlibStandardSet) covers
# most of these tokens redundantly, and this scan survives it for two
# calibrated reasons. First, `linter.style.nativeDecide` only runs in modules
# that (transitively) import it: `decide +native` inside an `example` in a
# slim-import module (`Basic`, `Observability`) elaborates with no warning,
# no linter, and no audit entry — demonstrated 2026-07-29; this scan is the
# only gate that sees it. Second, the pre-commit `proof-tokens` hook runs
# this scan on staged sources even when the verify hook is skipped, so a
# `SKIP=verify` commit keeps one fast proof-token gate.
#
# String literals are consumed whole before any comment test: `--` and `/-`
# inside a literal are content, not comment openers. Treating them as openers
# stripped the rest of the line and hid any proof token after a string such as
# `"a -- b"` (regression: tests/negative/StringSorryFixture.lean; the shapes
# the scanner must NOT flag are pinned by tests/positive/ScannerCorpus.lean).
def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and src[i] == '"':
            out.append(src[i])
            i += 1
            while i < n:
                c = src[i]
                out.append(c)
                i += 1
                if c == "\\" and i < n:
                    out.append(src[i])
                    i += 1
                elif c == '"':
                    break
        elif depth == 0 and two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        else:
            # Newlines survive inside comments so reported line numbers match
            # the original file.
            if depth == 0 or src[i] == "\n":
                out.append(src[i])
            i += 1
    return "".join(out)


# `sorryAx` before `sorry` so the longer token wins; `stop` is Mathlib's
# comment-out-the-rest tactic (it expands to sorry); `\+\s*native` catches
# `decide +native`, the config-flag spelling of `native_decide` (which
# elaborates with no warning at all inside an `example`). All three evaded
# the previous pattern (demonstrated 2026-07-26; fixtures pin each).
TOKEN_RE = re.compile(
    r"(?<![\w.])(sorryAx|sorry|admit|native_decide|stop)(?![\w'])"
    r"|\+\s*(native)(?![\w'])")


def scan_tokens(path):
    """Yield (line-number, token) for each proof token in `path`."""
    code = strip_comments(Path(path).read_text(encoding="utf-8"))
    for i, line in enumerate(code.splitlines(), 1):
        m = TOKEN_RE.search(line)
        if m:
            yield i, m.group(1) or "+native"


# `checks.py --scan FILE...` scans the named files and exits 1 if any carries a
# proof token. Used by the test driver to run this gate directly: a `sorry`
# inside an `example` only warns in Lean, so it cannot be an
# expected-elaboration-failure fixture like the others.
if len(sys.argv) > 1 and sys.argv[1] == "--scan":
    hits = [(f, i, t) for f in sys.argv[2:] for i, t in scan_tokens(f)]
    for f, i, t in hits:
        print(f"proof-token: {f}:{i} carries `{t}`")
    sys.exit(1 if hits else 0)

root = Path(sys.argv[1])
vdir = root / ".verify"
vdir.mkdir(exist_ok=True)
lean_files = sorted((root / "Overload").glob("**/*.lean"))
failures = []  # (check, detail)

# --- proof tokens: the zero-sorry claim, enforced at the source level
# (see scan_tokens above for why the environment sweep cannot do this).
for f in lean_files:
    for i, tok in scan_tokens(f):
        failures.append(("proof-tokens",
                         f"{f.relative_to(root)}:{i} carries `{tok}`"))
print(f"proof-tokens: {len(lean_files)} modules scanned for sorry/admit/native_decide")

# --- verdict
ledger = vdir / "DISCREPANCIES.md"
if failures:
    with ledger.open("w", encoding="utf-8") as fh:
        fh.write("# verify run findings\n")
        for check, detail in failures:
            fh.write(f"\n## {check}\n- {detail}\n- disposition: PENDING\n")
    for check, detail in failures:
        print(f"FAIL [{check}] {detail}", file=sys.stderr)
    sys.exit(1)
ledger.unlink(missing_ok=True)
print("docs-sync: all hard checks green")
