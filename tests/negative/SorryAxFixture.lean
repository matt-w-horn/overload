import Overload.Basic

/-!
Fixture for a third gap in the source-level `proof-tokens` gate.

`sorryAx` is the axiom behind `sorry`, and it can be applied directly without
ever spelling the surface token: inside an `example` the environment sweep
cannot see the axiom (Lean never adds an `example` to the environment), and a
token pattern for `sorry` alone does not match `sorryAx` — the trailing `A`
defeats the word boundary. Demonstrated evading the scanner on 2026-07-26.

Like `ExampleSorryFixture.lean` this fixture **compiles** (an `example` using
`sorryAx` only warns), so it is not an expected-elaboration-failure. What must
reject it is `checks.py --scan`, exercised by the test driver.
-/

namespace Overload

example : (2 : Nat) + 2 = 5 := sorryAx _ true

end Overload
