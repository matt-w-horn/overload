import Overload.Basic
import Overload.Amplification
import Overload.AttemptDist
import Overload.Burst
import Overload.Compose
import Overload.Operator
import Overload.Conservation
import Overload.Deadline
import Overload.Plateau
import Overload.Bistability
import Overload.Calculus
import Overload.Breaker
import Overload.MM1
import Overload.Little
import Overload.Erlang
import Overload.Coupling
import Overload.Star
import Overload.Composition
import Overload.Scheme
import Overload.CoupledStack
import Overload.Tightness
import Overload.Signature
import Overload.Priority
import Overload.Discipline
import Overload.Resources
import Overload.Observability
import Overload.Spec
import Overload.Universality
import Overload.Hysteresis
import Overload.Eligibility
import Overload.Autoscaling
import Overload.Witnesses
import Overload.Examples.SQS
import Overload.Examples.Borg
import Overload.Examples.Thrashing
import Overload.Examples.Pipeline
import Overload.Examples.Deficit
import Overload.Examples.Mesh

/-!
# Axiom audit

Three commands enforce the honesty claims the docstrings cannot:

* `#axiom_budget foo` checks a single declaration.
* `#axiom_budget_all Overload` sweeps the declarations of the environment
  whose name root is `Overload` (internal `_`-prefixed auxiliaries skipped,
  compiler-generated equation/match lemmas included).
* `#omitted_audit Overload` is the negative-space complement: the results the
  library deliberately *omits* rather than axiomatizes must actually be
  absent — no declaration under the namespace may carry one of the
  omitted-result name tokens.

The axiom commands fail the build unless every axiom the declaration depends
on is one of the three classical axioms Mathlib itself rests on (`propext`,
`Classical.choice`, `Quot.sound`). Any `sorry` introduces `sorryAx`, any
`native_decide` introduces a per-declaration trust axiom
(`<decl>._native.native_decide.ax_*`), and any custom `axiom`
introduces itself — each fails the build here. This file is part of the
default build target, so the claims are machine-checked, not aspirational.

## What the sweep does not reach

Two limits, both covered outside `lake build`:

* The environment holds only what this file *imports*, and the import list
  above is hand-maintained — a module missing from it is silently unswept.
  Nothing in `lake build` enforces the list; the `import-roots` check in
  `scripts/checks.py` does, by requiring every module under
  `Overload/` to appear in both this file and `Overload.lean`.
* Lean never adds an `example` to the environment, so no name-based sweep can
  see one: a `sorry` inside an `example` compiles and leaves the count below
  unchanged. The source-level `proof-tokens` scan in `checks.py` is what
  rejects it, and `tests/negative/ExampleSorryFixture.lean` is the fixture
  holding that gate shut.
-/

open Lean Elab Command in
/-- `#axiom_budget foo` fails elaboration unless every axiom `foo` depends on
is one of `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#axiom_budget " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let axs ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in axs do
    unless allowed.contains ax do
      throwError "axiom budget exceeded: {n} depends on {ax}"

open Lean Elab Command in
/-- `#axiom_budget_all Overload` runs the axiom-budget check on every
declaration in the environment whose name root is the given namespace,
skipping `_`-prefixed internal auxiliaries. No registration step is needed for
a new declaration, but the environment reaches only what this file imports and
never contains an `example` (see the module docstring); the checked count is
reported so the sweep's reach is visible in the build log. -/
elab "#axiom_budget_all " pfx:ident : command => do
  let env ← getEnv
  let root := pfx.getId
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    if n.getRoot == root && !n.isInternal then
      let axs ← collectAxioms n
      for ax in axs do
        unless allowed.contains ax do
          throwError "axiom budget exceeded: {n} depends on {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "#axiom_budget_all: no declarations found under `{root}`"
  logInfo m!"#axiom_budget_all: {checked} declarations under `{root}` are within the axiom budget"

namespace Overload

/-- The deliberately-omitted result families, as name tokens. Each names
analysis the library scopes out rather than axiomatizes:
`exitTime` (Freidlin–Wentzell/Kramers exit times),
`fluidFlow` (Kurtz fluid limits and ODE flow), `sojournDistribution` (the
open-loop sojourn law behind `mm1Kernel` — a modeling definition, not a
derived theorem), `PASTA` (the PASTA theorem; the lowercase `pasta`
*interface field* in `Spec` is the hypothesis, deliberately present and
deliberately not matched), `retrialQueue` (M/M/1 retrial closed forms),
`foldBifurcation` (crossing-count geometry), `limitCycle` (circuit-breaker
cycles). Matching is case-sensitive substring over fully-qualified names. -/
def overloadOmittedTokens : List String :=
  ["exitTime", "fluidFlow", "sojournDistribution", "PASTA", "retrialQueue",
    "foldBifurcation", "limitCycle"]

end Overload

open Lean Elab Command in
/-- `#omitted_audit Overload` fails elaboration if any declaration under the
given namespace root carries one of `Overload.overloadOmittedTokens` in its
name.
Complement of `#axiom_budget_all`: that sweep checks that everything present
is honestly proved; this one checks that what the documentation declares
absent is actually absent — "omitted, never axiomatized" as a build fact. -/
elab "#omitted_audit " pfx:ident : command => do
  let env ← getEnv
  let root := pfx.getId
  let mut scanned : Nat := 0
  for (n, _) in env.constants.toList do
    if n.getRoot == root && !n.isInternal then
      for tok in Overload.overloadOmittedTokens do
        if ((toString n).splitOn tok).length != 1 then
          throwError "omitted-name audit failed: `{n}` carries the omitted-result token `{tok}`"
      scanned := scanned + 1
  if scanned == 0 then
    throwError "#omitted_audit: no declarations found under `{root}`"
  logInfo m!"#omitted_audit: {scanned} declarations under `{root}` avoid the omitted-result tokens"

-- Smoke test of the single-name command on a Mathlib theorem.
#axiom_budget Nat.add_comm

-- The environment sweep: every imported declaration under `Overload` is
-- inside the budget or the build fails. Its two blind spots (the import list,
-- `example`s) are checked by `checks.py`, not here.
#axiom_budget_all Overload

-- The negative-space sweep: the deliberately-omitted results are absent by
-- machine check, not only by prose.
#omitted_audit Overload
