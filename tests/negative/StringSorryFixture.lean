import Overload.Basic

/-!
Fixture for the second gap in the source-level `proof-tokens` gate.

The scanner in `scripts/checks.py` strips comments before
looking for proof tokens. A `--` inside a *string literal* is not a comment
opener, and a scanner that treats it as one discards the rest of the line —
including any `sorry` that follows. Combined with the `example` gap (see
`ExampleSorryFixture.lean`) that put a `sorry` past both gates: the
environment sweep cannot see an `example`, and the token scan could not see
this line.

Like `ExampleSorryFixture.lean` this fixture **compiles** (an `example` with
`sorry` only warns), so it is not an expected-elaboration-failure. What must
reject it is `checks.py --scan`, exercised by the test driver.
-/

namespace Overload

example : ("a -- b" : String).length = 6 := by sorry

end Overload
