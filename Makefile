# The Overload verification ritual: build, lint, lint-style, test, stamp.
# `make verify` runs on every commit as the pre-commit `verify` hook.
# Escape hatches, in the open by design: SKIP=verify git commit, or
# --no-verify; a skipped verify means `make verify` afterwards, not a
# smaller escape hatch. Mechanical stages only — the two semantic passes
# in scripts/CLAUDE.md follow a green run, scoped by
# .verify/changed_lean.txt. Stages fail fast; logs land in .verify/.

SHELL := /bin/bash

# What the silencing-guard diffs. The pre-commit hook reads the staged
# diff; CI overrides with a commit range, e.g.
#   make silencing-guard GUARD_DIFF="<base-sha>...HEAD"
GUARD_DIFF ?= --cached

.PHONY: verify build lint lint-style test tally-sync scope silencing-guard \
	leanchecker simp-audit

verify: build lint lint-style test tally-sync scope

build:
	@mkdir -p .verify
	@set -o pipefail; lake build --wfail 2>&1 | tee .verify/build.log
	@count=$$(grep -oE '#axiom_budget_all: [0-9]+ declarations' .verify/build.log | grep -oE '[0-9]+' | head -1); \
	if [ -z "$$count" ]; then echo "verify: printed audit count not found in the build log" >&2; exit 1; fi; \
	echo "verify: audit count $$count"

lint:
	@set -o pipefail; lake lint 2>&1 | tee .verify/linter.log

lint-style:
	@set -o pipefail; lake exe lint-style 2>&1 | tee .verify/lint-style.log

test:
	@set -o pipefail; lake test 2>&1 | tee .verify/test.log

# The class tally is printed twice from two differently-built
# environments: the build-time gate (#coverage_report, from Gate.lean's
# import-all list, replayed into the lake test log) and the runtime driver
# (manifest-tally, from importModules). Two printed totals with no
# comparison between them are two unchecked numbers — the 914-vs-919
# lesson — so compare the suffixes character-for-character.
tally-sync:
	@gate=$$(grep '#coverage_report: ' .verify/test.log | tail -1 | sed 's/.*#coverage_report: //'); \
	driver=$$(grep 'manifest-tally: ' .verify/test.log | tail -1 | sed 's/.*manifest-tally: //'); \
	if [ -z "$$gate" ]; then echo "tally-sync: no #coverage_report line in .verify/test.log" >&2; exit 1; fi; \
	if [ -z "$$driver" ]; then echo "tally-sync: no manifest-tally line in .verify/test.log" >&2; exit 1; fi; \
	if [ "$$gate" != "$$driver" ]; then \
	  echo "tally-sync: build-time gate and runtime driver tallies disagree:" >&2; \
	  echo "  gate:   $$gate" >&2; \
	  echo "  driver: $$driver" >&2; \
	  exit 1; \
	fi; \
	echo "tally-sync: gate and driver agree — $$driver"

# Stamp the verified tree and scope the semantic passes. `git stash create`
# snapshots tracked+staged content without touching anything; at a clean
# tree it prints nothing, in which case HEAD is the verified state.
scope:
	@base=""; \
	if [ -f .verify/stamp ]; then base=$$(cat .verify/stamp 2>/dev/null); git cat-file -e "$$base" 2>/dev/null || base=""; fi; \
	if [ -n "$$base" ]; then git diff --name-only "$$base" -- '*.lean' > .verify/changed_lean.txt; \
	else git diff --name-only HEAD -- '*.lean' > .verify/changed_lean.txt; fi; \
	echo "changed Lean files in scope: $$(wc -l < .verify/changed_lean.txt | tr -d ' ')"
	@snap=$$(git stash create "verify snapshot" 2>/dev/null); \
	if [ -z "$$snap" ]; then snap=$$(git rev-parse HEAD); fi; \
	echo "$$snap" > .verify/stamp; \
	echo "verify: PASS — stamped $$snap"; \
	echo "verify: mechanical stages green; run the two semantic passes in scripts/CLAUDE.md over .verify/changed_lean.txt"

# Anti-silencing gate, run on every commit before the ritual: a diff
# that adds a gate-silencing token to the library needs a deliberate
# sign-off (SKIP=silencing-guard), never a silent landing — the linter
# configuration is only as strong as the review gate on changes to it.
# Two sweeps: added .lean lines against the token list (tests/negative/ is
# the fixtures' home for these tokens and OverloadTest names what it scans
# for, so both are excluded), and any touched linter line in lakefile.toml,
# where removing an option silences it just as surely as a set_option.
silencing-guard:
	@hits=$$(git diff $(GUARD_DIFF) -U0 -- 'Overload.lean' 'Overload/*.lean' 'Overload/**/*.lean' 'tests/positive/*.lean' \
	  | grep -E '^\+[^+]' \
	  | grep -E 'set_option +(linter|debug)\.|set_option +[A-Za-z.]*maxHeartbeats|@\[nolint|@\[implemented_by|@\[extern|^\+ *((private|protected|public|noncomputable) +)*(axiom|unsafe|partial) '; true); \
	tomlhits=$$(git diff $(GUARD_DIFF) -U0 -- lakefile.toml | grep -E '^[-+].*linter\.'; true); \
	if [ -n "$$hits$$tomlhits" ]; then \
	  echo "silencing-guard: diff $(GUARD_DIFF) touches gate-silencing tokens;" >&2; \
	  echo "sign off with SKIP=silencing-guard if deliberate" >&2; \
	  if [ -n "$$hits" ]; then echo "$$hits" >&2; fi; \
	  if [ -n "$$tomlhits" ]; then echo "lakefile.toml linter lines:" >&2; echo "$$tomlhits" >&2; fi; \
	  exit 1; \
	fi; \
	echo "silencing-guard: no gate-silencing tokens in diff $(GUARD_DIFF)"

# Kernel re-check: leanchecker (shipped with the toolchain since v4.28.0)
# replays each Overload module's .olean through the kernel, imports
# trusted — the airtight backstop behind the elaborator. One invocation
# covers the library: the tool matches targets by name PREFIX and spawns
# one concurrent task per matched module (LeanChecker.lean:93,106-108 in
# the toolchain source), so `leanchecker Overload` already checks all of
# it — the old per-module loop re-checked everything on its first
# iteration. Concurrency is bounded only by LEAN_NUM_THREADS (default =
# cores), and each task's import replay peaks ~2.6 GB (measured
# 2026-07-31, ClosedLoop), so workers are budgeted by MEMORY, never by
# cores. Measured 2026-07-31 on this 16 GB / 10-core machine: the
# 10-worker default demanded ~52 GB and thrashed without finishing one
# module; 4 workers still churned 5 GB of swap at ~25% pool utilization;
# 1 worker replayed the whole library in 2m31s at 4.9 GB peak RSS —
# concurrent environments evict each other's pages, so past the memory
# budget, more workers is strictly slower. Default: hw.memsize / 5 GiB
# per worker, clamped to [1, cores]; override with LEANCHECKER_WORKERS=N
# (use 1 when other work holds memory; each worker wants ~5 GiB free).
# Prefix matching also picks up stale oleans of renamed modules from
# .lake/build — run `lake clean` first for an exact module set.
leanchecker:
	@set -e; \
	if [ -n "$(LEANCHECKER_WORKERS)" ]; then n="$(LEANCHECKER_WORKERS)"; \
	else \
	  mem_gb=$$(( $$(sysctl -n hw.memsize) / 1073741824 )); \
	  n=$$(( mem_gb / 5 )); \
	  ncpu=$$(sysctl -n hw.ncpu); \
	  if [ "$$n" -lt 1 ]; then n=1; fi; \
	  if [ "$$n" -gt "$$ncpu" ]; then n=$$ncpu; fi; \
	fi; \
	echo "leanchecker: replaying every Overload module ($$n workers)"; \
	LEAN_NUM_THREADS=$$n lake env leanchecker -v Overload; \
	echo "leanchecker: kernel accepts every Overload module"

# Advisory: the simpNF environment linter re-run with
# respectTransparency, which catches more defeq abuse but may
# false-positive — findings are questions, not failures. Re-run after
# adding @[simp] lemmas (clean over 804 declarations on 2026-07-29).
simp-audit:
	@mkdir -p .verify
	@printf 'import Overload\nimport Batteries.Tactic.Lint\n\nset_option linter.simpNF.respectTransparency true in\n#lint only simpNF in Overload\n' > .verify/simp_audit.lean
	lake env lean .verify/simp_audit.lean
	@rm -f .verify/simp_audit.lean
