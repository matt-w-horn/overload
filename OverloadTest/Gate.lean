module

public meta import Lean.Elab.Command
public meta import OverloadTest.Coverage
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
import all Overload.AxiomAudit
public import OverloadTest.Coverage

/-!
# The coverage gate

Elaborating this file runs the coverage report over the whole library, so
`lake test` (which builds the test driver, which imports this) fails on any
uncovered declaration. The class tally lands in the build log next to the
axiom audit's count.

The `#coverage_report` elaborator is defined here rather than in
`OverloadTest/Coverage.lean` because the helpers it reads serve two phases:
the test driver executable calls them at runtime, so they cannot be `meta`,
and a command elaborator cannot call same-module non-`meta` code — the
`meta import` of `Coverage` is what lifts them across. The library
imports are `import all`, one per module, because the consumption
graph walks proof bodies (`getUsedConstantsAsSet`) and anything less
strips them: an exported-level import replaces a theorem with a
signature stub, and `import all` does not propagate through the
`Overload` aggregator — resolved either of those ways, every bridge
entry reads as stale. The list is hand-maintained like the two audit
roots; the `import-roots` stage checks all three.
-/

@[expose] public section

meta section

open Lean Elab Command in
/-- `#coverage_report Overload` fails elaboration unless every non-exempt
declaration under the namespace is bridged, witnessed, consumed, or ledgered
terminal. Prints the class tally so coverage is a build-log fact. See the
module docstring for the classes and the ledgers in `OverloadTest.Ledger`. -/
elab "#coverage_report " pfx:ident : command => do
  let env ← getEnv
  let root := pfx.getId
  -- The graph and classification are `OverloadTest.computeCoverage` in
  -- `OverloadTest/Coverage.lean` — one code path with the manifest
  -- stamping. This elaborator's whole job is turning its findings into
  -- errors and printing the tally.
  let cov := OverloadTest.computeCoverage env root
  if cov.univ.isEmpty then
    throwError "#coverage_report: no declarations found under `{root}`"
  if let some f := cov.findings[0]? then
    throwError "#coverage_report: {f}"
  let acc := cov.tally
  let total := cov.univ.size
  let pct (k : Nat) : Nat := k * 100 / total
  unless acc.uncovered.isEmpty do
    let names := acc.uncovered.qsort (·.toString < ·.toString)
    throwError "#coverage_report: {acc.uncovered.size} uncovered (C0) declaration(s) under \
      `{root}`:{indentD (MessageData.joinSep (names.toList.map (m!"{·}")) Format.line)}"
  logInfo m!"#coverage_report: {total} declarations under `{root}` — \
    C4 bridged {acc.c4} ({pct acc.c4}%), C3 pinned {acc.c3} ({pct acc.c3}%), \
    C2 witnessed {acc.c2} ({pct acc.c2}%), C1 consumed {acc.c1} ({pct acc.c1}%), \
    terminal {acc.t} ({pct acc.t}%), C0 uncovered 0 \
    (exempt auto-generated: {cov.exempt})"

end

#coverage_report Overload
