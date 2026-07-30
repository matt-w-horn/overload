import Overload.Basic

/-!
Fixture for the one gap the environment sweep cannot close.

Lean never adds an `example` to the environment, so `#axiom_budget_all
Overload` cannot see this declaration: it elaborates with only a
`warning: declaration uses 'sorry'`, the sweep's printed count does not move,
and `lake build` exits 0. Verified 2026-07-24 — with this file's body spliced
into the library, the audit reported an unchanged declaration count.

Unlike the other three fixtures, this one is therefore **not** an
expected-elaboration-failure: it compiles. What must reject it is the
source-level `proof-tokens` gate in `scripts/checks.py`, which the test
driver exercises via `checks.py --scan`. The driver also elaborates it
and requires exit 0, pinning the compiles-with-only-a-warning property
this file's argument rests on. (The statement was `(1 : ℝ) + 1 = 2`
until 2026-07-29; it silently stopped elaborating when `Overload.Basic`
stopped importing ℝ's instances, and nothing noticed because no gate
elaborated this file. `Nat` keeps the fixture importing only
`Overload.Basic`.)
-/

namespace Overload

example : (2 : Nat) + 2 = 5 := by sorry

end Overload
