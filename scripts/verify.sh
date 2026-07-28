#!/usr/bin/env bash
# verify.sh — the Overload verification ritual: build, lint, test, stamp.
# Mechanical stages only; the two semantic passes in that README follow a
# green run, scoped by .verify/changed_lean.txt. Runs on every commit via
# the pre-commit `verify` hook; escape hatches: SKIP=verify, --no-verify.
set -uo pipefail

root=$(git rev-parse --show-toplevel) || exit 1
cd "$root"
mkdir -p .verify
verify_dir="scripts"
fail=0

echo "== [1/4] lake build"
if ! lake build 2>&1 | tee .verify/build.log; then fail=1; fi
count=$(grep -oE '#axiom_budget_all: [0-9]+ declarations' .verify/build.log | grep -oE '[0-9]+' | head -1 || true)
if [ -z "${count}" ]; then
  echo "verify: printed audit count not found in the build log" >&2
  fail=1
else
  echo "verify: audit count ${count}"
fi

echo "== [2/4] lake lint"
if ! lake lint 2>&1 | tee .verify/linter.log; then fail=1; fi

echo "== [3/4] lake test"
if ! lake test 2>&1 | tee .verify/test.log; then fail=1; fi

echo "== [4/4] change scope for the semantic passes"
base=""
if [ -f .verify/stamp ]; then
  base=$(cat .verify/stamp 2>/dev/null || true)
  git cat-file -e "$base" 2>/dev/null || base=""
fi
if [ -n "$base" ]; then
  git diff --name-only "$base" -- '*.lean' > .verify/changed_lean.txt || true
else
  git diff --name-only HEAD -- '*.lean' > .verify/changed_lean.txt || true
fi
echo "changed Lean files in scope: $(wc -l < .verify/changed_lean.txt | tr -d ' ')"

if [ "$fail" -ne 0 ]; then
  echo "verify: FAILED — see .verify/DISCREPANCIES.md and the logs in .verify/" >&2
  exit 1
fi

# Stamp the verified tree. `git stash create` snapshots tracked+staged
# content without touching anything; at a clean tree it prints nothing,
# in which case HEAD is the verified state.
snap=$(git stash create "verify snapshot" 2>/dev/null || true)
[ -z "$snap" ] && snap=$(git rev-parse HEAD)
echo "$snap" > .verify/stamp
echo "verify: PASS — stamped ${snap}"
echo "verify: mechanical stages green; run the two semantic passes in ${verify_dir}/README.md over .verify/changed_lean.txt"
