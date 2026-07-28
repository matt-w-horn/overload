import Overload.Basic

/-!
Fixture for a fifth gap in the source-level `proof-tokens` gate — the worst
of the three found on 2026-07-26, because it produces **no warning at all**.

`decide +native` is the config-flag spelling of `native_decide`: it trusts
the compiled evaluator (the `ofReduceBool` axiom) exactly as `native_decide`
does, but the token `native_decide` never appears. In a named theorem the
axiom audit catches the dependency; inside an `example` nothing does — the
file elaborates silently. `checks.py --scan` must reject it via the
`+native` pattern.
-/

namespace Overload

example : (2 : Nat) + 2 = 4 := by decide +native

end Overload
