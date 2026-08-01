module

public meta import Lean.Elab.Command
import all Overload.Basic
import all Overload.Retry.Amplification
import all Overload.Retry.AttemptDist
import all Overload.Dynamics.Burst
import all Overload.Retry.Compose
import all Overload.Loop.Operator
import all Overload.Capacity.Conservation
import all Overload.Retry.Deadline
import all Overload.Capacity.Plateau
import all Overload.Loop.ClosedLoop
import all Overload.Dynamics.Calculus
import all Overload.Control.Breaker
import all Overload.Queueing.MM1
import all Overload.Queueing.Little
import all Overload.Queueing.Erlang
import all Overload.Stack.Coupling
import all Overload.Stack.Star
import all Overload.Retry.Composition
import all Overload.Stack.Scheme
import all Overload.Stack.CoupledStack
import all Overload.Stack.Tightness
import all Overload.Loop.Signature
import all Overload.Control.Priority
import all Overload.Control.Discipline
import all Overload.Capacity.Resources
import all Overload.Control.Observability
import all Overload.Verification.Suite
import all Overload.Loop.Universality
import all Overload.Loop.Hysteresis
import all Overload.Loop.Eligibility
import all Overload.Control.Autoscaling
import all Overload.Verification.Witnesses
import all Overload.Examples.SQS
import all Overload.Examples.Borg
import all Overload.Examples.Thrashing
import all Overload.Examples.Pipeline
import all Overload.Examples.Deficit
import all Overload.Examples.Mesh
import all Overload.Lint
public import Lean.Exception

/-!
# Axiom audit

Three commands enforce the honesty claims the docstrings cannot:

* `#axiom_budget foo` checks a single declaration.
* `#axiom_budget_all Overload` sweeps the declarations of the environment
  whose name root is `Overload` (internal `_`-prefixed auxiliaries skipped,
  compiler-generated equation/match lemmas included).
* `#omitted_audit Overload` is the negative-space complement: the results the
  library deliberately *omits* rather than axiomatizes must actually be
  absent — no declaration under the namespace carries one of the
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
  Nothing in `lake build` enforces the list. The `import-roots` check in
  `OverloadTest/Main.lean` does, by requiring every module under
  `Overload/` to appear in both this file and `Overload.lean`. The imports
  are `import all` because a plain `import` resolves at the exported level,
  which omits `private` declarations from the environment entirely — a
  `sorry` behind `private` is then invisible rather than caught
  (`tests/negative/PrivateSorryFixture.lean` holds this shut, together with
  `inAuditedNamespace` below).
* Lean never adds an `example` to the environment, so no name-based sweep can
  see one: a `sorry` inside an `example` compiles and leaves the count below
  unchanged. The source-level `proof-tokens` scan in `checks.py` is what
  rejects it, and `tests/negative/ExampleSorryFixture.lean` is the fixture
  holding that gate shut.
-/

-- `public` without `@[expose]`: nothing here is proof-relevant, and an
-- unexposed public body can reference the `private` predicate below where
-- an exposed one cannot.
public section

-- The audit commands run at elaboration time, so under the module system
-- they are `meta`, the shape of Mathlib's linter files. The predicate they
-- read sits inside the section with them; see its docstring.
meta section

/-- Whether a constant belongs to the audited namespace. Private
declarations reach the environment mangled as `_private.<Module>.<n>.<Name>`,
whose root is `_private` and which `isInternal` reports true, so a bare
`n.getRoot == root` check silently skips them.
`Lean.privateToUserName` un-mangles first. It is the identity on non-private
names, so this is a strict widening of the old rule and leaves today's count
unmoved. Load-bearing only once the library is on the module system, where a
`private` declaration is what a `sorry` can hide behind. Measured
2026-07-29 against a probe module: the old rule saw 1 of 2
declarations and reported the `sorry`-tainted one as clean.

`OverloadTest/Coverage.lean`'s `auditRule` carries a copy of these two
lines (read by the coverage gate and the test driver), because the module
system's phase separation runs both ways: a `meta` definition cannot
reference a non-meta one, so this cannot be hoisted out of the section
below for a plain `def` to share. The copy must agree with this one — they
disagreed on 2026-07-29 (914 against 919) and nothing caught it, because
two printed totals with no comparison between them are not checked.

`private`, deliberately: the three commands below are its only readers, and
a public root-level name here would land an unqualified `inAuditedNamespace`
in the namespace of anyone who writes `import Overload`. Either way it sits
outside the sweeps it powers — its name root is not `Overload` — so the
gates on it are this docstring and `tests/negative/PrivateSorryFixture.lean`,
not the audit. -/
private def inAuditedNamespace (root n : Lean.Name) : Bool :=
  let u := Lean.privateToUserName n
  u.getRoot == root && !u.isInternal

namespace Overload

/-- The deliberately-omitted result families, as name tokens. Each names
analysis the library scopes out rather than axiomatizes:
`exitTime` (Freidlin–Wentzell/Kramers exit times),
`fluidFlow` (Kurtz fluid limits and ODE flow), `sojournDistribution` (the
open-loop sojourn law behind `mm1Kernel` — a modeling definition, not a
derived theorem), `PASTA` (the PASTA theorem; the lowercase `pasta`
*interface field* in `VerificationSuite` is the hypothesis, deliberately present and
deliberately not matched), `retrialQueue` (M/M/1 retrial closed forms),
`foldBifurcation` (crossing-count geometry), `limitCycle` (circuit-breaker
cycles). Matching is case-sensitive substring over fully-qualified names. -/
def overloadOmittedTokens : List String :=
  ["exitTime", "fluidFlow", "sojournDistribution", "PASTA", "retrialQueue",
    "foldBifurcation", "limitCycle"]

end Overload

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
  logInfo m!"#axiom_budget: {n} is within the axiom budget"

open Lean Elab Command in
/-- `#axiom_budget_all Overload` runs the axiom-budget check on every
declaration in the environment whose name root is the given namespace,
skipping internal auxiliaries but *not* private declarations (see
`inAuditedNamespace`). No registration step is needed for
a new declaration, but the environment reaches only what this file imports and
never contains an `example` (see the module docstring). The checked count is
reported so that the sweep's reach is visible in the build log. -/
elab "#axiom_budget_all " pfx:ident : command => do
  let env ← getEnv
  let root := pfx.getId
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    if inAuditedNamespace root n then
      let axs ← collectAxioms n
      for ax in axs do
        unless allowed.contains ax do
          throwError "axiom budget exceeded: {n} depends on {ax}"
      checked := checked + 1
  if checked == 0 then
    throwError "#axiom_budget_all: no declarations found under `{root}`"
  logInfo m!"#axiom_budget_all: {checked} declarations under `{root}` are within the axiom budget"

open Lean Elab Command in
/-- `#omitted_audit Overload` fails elaboration if any declaration under the
given namespace root carries one of `Overload.overloadOmittedTokens` in its
name.
Complement of `#axiom_budget_all`: that sweep checks that everything present
is honestly proved. This one checks that what the documentation declares
absent is actually absent — "omitted, never axiomatized" as a build fact. -/
elab "#omitted_audit " pfx:ident : command => do
  let env ← getEnv
  let root := pfx.getId
  let mut scanned : Nat := 0
  for (n, _) in env.constants.toList do
    if inAuditedNamespace root n then
      -- Test the un-mangled name, matching the membership test above: the
      -- mangled `_private.<Module>.…` form carries the module path, so
      -- testing it fails every private declaration in a file whose name
      -- contains a token, with a message naming the declaration.
      for tok in Overload.overloadOmittedTokens do
        if ((toString (privateToUserName n)).splitOn tok).length != 1 then
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
