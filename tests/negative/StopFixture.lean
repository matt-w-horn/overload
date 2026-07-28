import Overload.Basic

/-!
Fixture for a fourth gap in the source-level `proof-tokens` gate.

Mathlib's `stop` tactic comments out the rest of a proof by closing every
remaining goal with `sorry` — without the token `sorry` appearing in the
source. Inside an `example` the environment sweep cannot see the resulting
`sorryAx` dependency. Demonstrated evading the scanner on 2026-07-26.

Compiles (warns); `checks.py --scan` must reject it. The word `stop` in
comments and docstrings is stripped before scanning, so prose like Scheme's
`(trigger, stop, timing, scope)` formalism stays legal — the corpus pins
identifier lookalikes (`stopped`, `unstoppable`).
-/

namespace Overload

example : (2 : Nat) + 2 = 5 := by stop exact rfl

end Overload
