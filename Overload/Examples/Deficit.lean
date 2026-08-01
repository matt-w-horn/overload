module

public import Overload.Basic -- shake: keep
public import Overload.Stack.Coupling
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

/-!
# Capacity deficit as a coupled site: supply degradation in the J-matrix

This file states the fourth sustaining mechanism (M4, supply degradation —
cold caches after restarts, GC pressure, compaction debt, connection
re-establishment) as a coupling instance. It gives M4 the concrete witness
the other three mechanisms already have (SQS for re-armed timeouts,
Thrashing for the clamp, CoupledStack for spill-in coupling).

Alongside the demand deviation (site 0), track the **capacity deficit**
(site 1) as its own state. Overload erodes supply — the demand → deficit
spill `ε₂₁` — and eroded supply amplifies demand — the deficit → demand
spill `ε₁₂`. The M4 feedback loop is exactly an off-diagonal product, and
the two-site certificate machinery decides it: no spectral computation,
just the spill product against the margin product (read at sustaining
mechanism M4).

* `deficit_certified` — the stable instance: both rows contract under the
  uniform weight vector.
* `deficit_floor_blocks` — heavy erosion (`ε₂₁ = 3/2`: each unit of
  overload costs one and a half units of effective capacity) crosses the
  floor, and *no* weight vector certifies the pair — supply degradation
  sustains the overload, whatever the demand side does.

The auditable pair is (deficit → demand sensitivity, demand → deficit
erosion). Reading a real system's numbers into the matrix entries is the
modeling step, as in `Coupling.lean`.
-/

@[expose] public section

namespace Overload

/-- **M4, certified stable.** Local gains `1/2` (retry response) and `3/10`
(deficit persistence), cross-couplings `2/5` (deficit inflates demand) and
`1/2` (demand erodes capacity): both rows contract under uniform weights —
`1/2 + 2/5 = 9/10 < 1` and `1/2 + 3/10 = 4/5 < 1`. -/
theorem deficit_certified : Certificate !![1/2, 2/5; 1/2, 3/10] :=
  certificate_of_two (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_pos one_pos (by norm_num) (by norm_num)

/-- **M4, sustaining.** With erosion `ε₂₁ = 3/2` the spill product
`2/5 · 3/2 = 3/5` crosses the margin product `(1 − 1/2)(1 − 3/10) = 7/20`:
no positive weight vector certifies the pair (`spill_floor_blocks`). The
mechanism audit's M4 leg, quantitatively: this is what "the overload is
sustained by supply degradation" looks like in the coupling algebra. -/
theorem deficit_floor_blocks : ¬Certificate !![1/2, 2/5; 3/2, 3/10] :=
  spill_floor_blocks (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Overload
