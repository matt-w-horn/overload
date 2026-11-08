# Upstream/

Copies of this library's open mathlib pull requests, trimmed to what the
library uses, so that it can use the mathlib formulations before they
reach a mathlib release. Each file sits at its mathlib path with `Mathlib/`
replaced by `Upstream/`, so module `Upstream.X` is the future `Mathlib.X`.
The declaration names, namespaces, and signatures are mathlib's.

| File | mathlib PR | Used by |
|---|---|---|
| `Order/FixedPointsIcc.lean` | [#42225](https://github.com/leanprover-community/mathlib4/pull/42225) | `Overload/Loop/Operator.lean` |
| `Analysis/SpecialFunctions/ErlangB.lean` | [#42382](https://github.com/leanprover-community/mathlib4/pull/42382) | `Overload/Queueing/Erlang.lean` |
| `Analysis/SpecificLimits/Counting.lean` | [#42384](https://github.com/leanprover-community/mathlib4/pull/42384) | `Overload/Queueing/Little.lean` |
| `Probability/Distributions/GeometricCensored.lean` | [#42381](https://github.com/leanprover-community/mathlib4/pull/42381) | `Overload/Retry/AttemptDist.lean` |
| `Probability/Distributions/Geometric.lean` | [#45786](https://github.com/leanprover-community/mathlib4/pull/45786) | `GeometricCensored.lean` above |

A file keeps only the declarations the `Overload` library reaches, directly
or through another kept declaration's proof. The kept declarations are
verbatim except where noted below, and the module docstring drops the
lines that name what was cut. The cuts:

- `Order/FixedPointsIcc.lean`: `isLeast_lfpIcc` and its generated dual
  `isGreatest_gfpIcc`.
- `Analysis/SpecialFunctions/ErlangB.lean`: `Real.erlangB_mul_sum` and
  `Real.erlangB_eq_div` (the closed form), and the three imports only they
  needed. Its proofs also differ in one way: `erlangB_nonneg`,
  `erlangB_denom_pos`, and `erlangB_le_one` pass to `linarith` the facts
  #42382 states as `have` lines, because this library's
  `linter.unusedVariables.analyzeTactics` counts a `have` that only
  `linarith` consumes as unused. The statements are verbatim.
- `Probability/Distributions/Geometric.lean`: everything but the two lemmas
  #45786 adds to mathlib's existing file of that name
  (`geometricMeasure_Iio`, `geometricMeasure_Ici`). The header, imports, and
  namespace lines around them are new.
- `Probability/Distributions/GeometricCensored.lean`: nothing cut, but it
  imports `Upstream.Probability.Distributions.Geometric` where #42381
  imports `Mathlib.Probability.Distributions.Geometric`, so that it sees
  those two lemmas.

When a pull request merges and the mathlib pin reaches it, delete its file
here and change each `import Upstream.X` to `import Mathlib.X`. Nothing else
changes. For #45786, delete `Geometric.lean` and drop the changed import
line from `GeometricCensored.lean`.

These files build as the `Upstream` library, outside `Overload/` and its
gates (statement lock, claims ledger, coverage, `lake lint`): they follow
mathlib's conventions, and mathlib review is their gate. The library's own
linter options apply to them. The axiom audit reaches every vendored
declaration, because each one is used by an `Overload` declaration that
depends on it.
