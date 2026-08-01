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
	leanchecker watcher-tools nanoda simp-audit

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

# The driver elaborates eleven expected-failure fixtures, each its own `lean`
# process loading the Mathlib oleans, so the same memory budget applies; the
# driver's own default is deliberately conservative for a bare `lake test`.
test:
	@set -e; \
	if [ -n "$(TEST_JOBS)" ]; then n="$(TEST_JOBS)"; \
	else $(worker_budget); fi; \
	set -o pipefail; OVERLOAD_TEST_JOBS=$$n lake test 2>&1 | tee .verify/test.log

# The class tally is printed twice from two differently-built
# environments: the build-time gate (#coverage_report, from Gate.lean's
# import-all list, replayed into the lake test log) and the runtime driver
# (manifest-tally, from importModules). Two printed totals with no
# comparison between them are two unchecked numbers — the 914-vs-919
# lesson — so compare the suffixes character-for-character. The audit
# count has the same shape: `inAuditedNamespace` (Overload/AxiomAudit.lean)
# and its documented copy `auditRule` (OverloadTest/Coverage.lean) each
# print a declaration count, and the 914-vs-919 disagreement WAS those two
# predicates drifting — so the second block compares them too.
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
	@audit=$$(grep -oE '#axiom_budget_all: [0-9]+ declarations' .verify/build.log | grep -oE '[0-9]+' | tail -1); \
	rule=$$(grep -oE 'audit-rule count [0-9]+' .verify/test.log | grep -oE '[0-9]+' | tail -1); \
	if [ -z "$$audit" ]; then echo "tally-sync: no #axiom_budget_all count in .verify/build.log" >&2; exit 1; fi; \
	if [ -z "$$rule" ]; then echo "tally-sync: no audit-rule count in .verify/test.log" >&2; exit 1; fi; \
	if [ "$$audit" != "$$rule" ]; then \
	  echo "tally-sync: build-time axiom audit and driver audit-rule counts disagree:" >&2; \
	  echo "  #axiom_budget_all: $$audit" >&2; \
	  echo "  audit-rule count:  $$rule" >&2; \
	  exit 1; \
	fi; \
	echo "tally-sync: audit counts agree — $$audit"

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
# Four sweeps: added .lean lines against the token list (tests/negative/ is
# the fixtures' home for these tokens and OverloadTest names what it scans
# for, so both are excluded); any touched linter line in lakefile.toml,
# where removing an option silences it just as surely as a set_option;
# any touched line at all in the gate carriers that nothing else watches
# (.pre-commit-config.yaml, the workflows, Overload/Lint.lean, and this
# Makefile, which holds every sweep below — rare-change files, so the
# sign-off friction is a few times a month at most); and the two
# load-bearing lines other gates rest on — checks.py's token regex and
# AxiomAudit's axiom allowlist. In CI the sign-off is the
# silencing-signed-off label on the PR (ci.yml skips the mirror job).
silencing-guard:
	@hits=$$(git diff $(GUARD_DIFF) -U0 -- 'Overload.lean' 'Overload/*.lean' 'Overload/**/*.lean' 'tests/positive/*.lean' \
	  | grep -E '^\+[^+]' \
	  | grep -E 'set_option +(linter|debug)\.|set_option +[A-Za-z.]*maxHeartbeats|@\[nolint|@\[implemented_by|@\[extern|^\+ *((private|protected|public|noncomputable) +)*(axiom|unsafe|partial) '; true); \
	tomlhits=$$(git diff $(GUARD_DIFF) -U0 -- lakefile.toml | grep -E '^[-+].*linter\.'; true); \
	gatehits=$$(git diff $(GUARD_DIFF) -U0 -- .pre-commit-config.yaml '.github/workflows/*' Overload/Lint.lean Makefile \
	  | grep -E '^[-+]' | grep -vE '^(\+\+\+|---)'; true); \
	surfhits=$$(git diff $(GUARD_DIFF) -U0 -- scripts/checks.py Overload/AxiomAudit.lean \
	  | grep -E '^[-+]' | grep -vE '^(\+\+\+|---)' | grep -E 'TOKEN_RE|re\.compile| r"|allowed'; true); \
	if [ -n "$$hits$$tomlhits$$gatehits$$surfhits" ]; then \
	  echo "silencing-guard: diff $(GUARD_DIFF) touches gate-silencing tokens or gate files;" >&2; \
	  echo "sign off with SKIP=silencing-guard if deliberate" >&2; \
	  if [ -n "$$hits" ]; then echo "$$hits" >&2; fi; \
	  if [ -n "$$tomlhits" ]; then echo "lakefile.toml linter lines:" >&2; echo "$$tomlhits" >&2; fi; \
	  if [ -n "$$gatehits" ]; then echo "gate-carrier lines:" >&2; echo "$$gatehits" >&2; fi; \
	  if [ -n "$$surfhits" ]; then echo "token-regex / allowlist lines:" >&2; echo "$$surfhits" >&2; fi; \
	  exit 1; \
	fi; \
	echo "silencing-guard: no gate-silencing tokens in diff $(GUARD_DIFF)"

# Concurrent Lean processes are budgeted by MEMORY, never by cores: each one
# replays the Mathlib imports and peaks at gigabytes, and past the memory
# budget concurrent environments evict each other's pages, so more workers is
# strictly slower. The measurements behind the 5 GiB-per-worker figure are in
# the leanchecker note below. Sets $$n; every caller checks its own override
# variable first.
define worker_budget
	  if command -v sysctl >/dev/null 2>&1 && sysctl -n hw.memsize >/dev/null 2>&1; then \
	    mem_gb=$$(( $$(sysctl -n hw.memsize) / 1073741824 )); \
	    ncpu=$$(sysctl -n hw.ncpu); \
	  else \
	    mem_gb=$$(( $$(awk '/MemTotal/ {print $$2}' /proc/meminfo) / 1048576 )); \
	    ncpu=$$(nproc); \
	  fi; \
	  n=$$(( mem_gb / 5 )); \
	  if [ "$$n" -lt 1 ]; then n=1; fi; \
	  if [ "$$n" -gt "$$ncpu" ]; then n=$$ncpu; fi
endef

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
	else $(worker_budget); fi; \
	echo "leanchecker: replaying every Overload module ($$n workers)"; \
	LEAN_NUM_THREADS=$$n lake env leanchecker -v Overload; \
	echo "leanchecker: kernel accepts every Overload module"

# Independent second watcher: Nanoda, a from-scratch Rust implementation
# of the Lean kernel, checking the library's lean4export NDJSON export.
# This is what the toolchain's own leanchecker cannot give: a kernel bug
# replays identically there (same code, same pin), while an independent
# implementation with its own arithmetic has to be wrong in the same way
# at the same time. Pins: lean4export at its v4.32.0-toolchain rev with
# this repo's lean-toolchain copied over it (the export runtime must
# match the oleans it reads, and a patch release is source-compatible);
# nanoda_lib at the Lean Kernel Arena's rev. Axiom policy is
# deliberately open (the Arena's own setting): the export necessarily
# declares Lean core's own axioms (trustCompiler, ofReduceBool, sorryAx)
# and core meta-code references them, so a whitelist either hard-errors
# on the declarations or panics on the dangling references — both
# demonstrated 2026-08-01. Library axiom discipline is
# #axiom_budget_all's job, per declaration at build time; this leg
# contributes independent TYPE-CHECKING, and the nat/string kernel
# extensions are nanoda's own implementations, which is the point.
# Checkouts, config, and the export live OUTSIDE the
# working tree, under ~/.cache: anything that treats the tree as
# disposable (a clean checkout, a sync, a worktree) clobbers a nested
# clone's .git, after which git commands inside it silently answer for
# the enclosing repo instead. The export covers the full dependency
# cone — Mathlib included, unlike leanchecker's trusted imports — so
# this is a heavyweight target: run it where compute is cheap (CI, a
# build host), not per commit.
LEAN4EXPORT_REV := 4e7915201d3f9f04470d9eae002fa695f7cdc589
NANODA_REV := ddfac2bf5a7b56cb46e141494427ff3dd55963c7
WATCHERS := $(HOME)/.cache/overload-watchers

watcher-tools:
	@mkdir -p $(WATCHERS)
	@if [ ! -d $(WATCHERS)/lean4export ]; then \
	  git clone -q https://github.com/leanprover/lean4export $(WATCHERS)/lean4export; \
	fi
	@cd $(WATCHERS)/lean4export && git fetch -q origin && git checkout -q -f $(LEAN4EXPORT_REV)
	@cp lean-toolchain $(WATCHERS)/lean4export/lean-toolchain
	@set -o pipefail; cd $(WATCHERS)/lean4export && lake build 2>&1 | tail -1
	@if [ ! -d $(WATCHERS)/nanoda_lib ]; then \
	  git clone -q https://github.com/ammkrn/nanoda_lib $(WATCHERS)/nanoda_lib; \
	fi
	@cd $(WATCHERS)/nanoda_lib && git fetch -q origin && git checkout -q -f $(NANODA_REV)
	@set -o pipefail; cd $(WATCHERS)/nanoda_lib \
	  && PATH="$$HOME/.cargo/bin:$$PATH" cargo build --release 2>&1 | tail -1
	@printf '%s\n' \
	  '{' \
	  '  "use_stdin": true,' \
	  '  "nat_extension": true,' \
	  '  "string_extension": true,' \
	  '  "unsafe_permit_all_axioms": true,' \
	  '  "unpermitted_axiom_hard_error": false,' \
	  '  "print_success_message": true,' \
	  '  "num_threads": 4' \
	  '}' > $(WATCHERS)/nanoda-config.json
	@echo "watcher-tools: lean4export and nanoda_bin built at their pins"

nanoda: watcher-tools
	@echo "nanoda: exporting the Overload cone (Mathlib included)"
	mkdir -p $(WATCHERS) && lake env $(WATCHERS)/lean4export/.lake/build/bin/lean4export Overload > $(WATCHERS)/export.ndjson
	@test -s $(WATCHERS)/export.ndjson \
	  || { echo "nanoda: export is missing or empty" >&2; exit 1; }
	@set -o pipefail; wc -c < $(WATCHERS)/export.ndjson | awk '{printf "nanoda: export is %d bytes\n", $$1}'
	@# Self-calibration on every run: a checker that accepts a corrupted
	@# export inspects nothing, so stream a corrupted copy (every Nat
	@# reference becomes Bool) and require rejection before the real
	@# verdict counts. Streamed rather than written: the export is
	@# gigabytes, and a temp copy would double the disk footprint and
	@# leak on the failure path.
	@if sed 's/Nat/Bool/g' $(WATCHERS)/export.ndjson \
	    | $(WATCHERS)/nanoda_lib/target/release/nanoda_bin $(WATCHERS)/nanoda-config.json >/dev/null 2>&1; then \
	  echo "nanoda: DOCTORED export accepted — the checker inspects nothing" >&2; \
	  exit 1; \
	fi
	@echo "nanoda: doctored export rejected (self-calibration passed)"
	$(WATCHERS)/nanoda_lib/target/release/nanoda_bin $(WATCHERS)/nanoda-config.json < $(WATCHERS)/export.ndjson
	@echo "nanoda: independent kernel accepts the export"

# Advisory: the simpNF environment linter re-run with
# respectTransparency, which catches more defeq abuse but may
# false-positive — findings are questions, not failures. Re-run after
# adding @[simp] lemmas (clean over 804 declarations on 2026-07-29).
simp-audit:
	@mkdir -p .verify
	@printf 'import Overload\nimport Batteries.Tactic.Lint\n\nset_option linter.simpNF.respectTransparency true in\n#lint only simpNF in Overload\n' > .verify/simp_audit.lean
	lake env lean .verify/simp_audit.lean
	@rm -f .verify/simp_audit.lean
