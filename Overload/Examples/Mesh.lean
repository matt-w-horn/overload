module

public import Overload.Basic -- shake: keep
public import Overload.Stack.Scheme
public import Overload.Stack.Coupling
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

/-!
# Mesh: two regions, two tiers — retry stacks feeding a spill matrix

The standard multi-region deployment (a founding target: any-to-any
service meshes, Spanner-style regional serving): each region runs a
two-tier retry stack, and regions fail over into each other. The two
altitudes of the library compose:

* **Within a region** the stack is the `Scheme` object: per-tier caps
  multiply (`layersAmp_le_prod_cap`), and `λ·∏capᵢ < C` certifies the
  region in isolation (`stack_budget_no_congestedEq`).
* **Across regions** deviations couple through failover spill, and joint
  stability is the `Coupling` certificate on the 2×2 matrix.

**The stitching, stated honestly.** The J-matrix entries are modeling
inputs, not theorems. The worked instance reads each region's local gain
as its amplified worst-case utilization `γᵣ := λᵣ·∏capᵢ/Cᵣ` — the same
number the stack-budget certificate bounds — and the off-diagonals as
failover fractions. Everything downstream of that reading is certified;
the reading itself is the modeling step (the same interface stance as
`mm1Kernel` and PASTA). Worst-case stacks are taken at `p = 1`, where a
layer's amplification *equals* its cap (Mathlib's `one_geom_sum`), so the cap
product is attained, not just an upper bound.

Worked instance: region 1 at `λ = 2` with tier caps `3 × 2` against
`C = 20` (`γ₁ = 2·6/20 = 3/5`); region 2 at `λ = 3/2` with caps `2 × 2`
against `C = 20` (`γ₂ = 3/2·4/20 = 3/10`); failover spill `1/5` each way.

* `region1Stack` / `region2Stack` — the worst-case stacks; their
  amplifications close to `6` and `4` by the eval lemma.
* `mesh_certified` — spill product `1/25` against margin product
  `(2/5)(7/10) = 7/25`: the mesh is jointly stable, by uniform weights.
* `mesh_fixed_fraction_blocked` — failing over a *fixed* `3/5` of load
  regardless of the target's headroom crosses the floor (`9/25 ≥ 7/25`):
  no certificate at any weights. Fail over by the target's headroom,
  never by a fixed fraction — the headroom rule, at mesh scale.
-/

@[expose] public section

namespace Overload

/-- Region 1's worst-case retry stack: tier caps `3` and `2` at `p = 1`
(every attempt fails — amplification equals the cap). -/
noncomputable abbrev region1Stack : List Layer :=
  [⟨1, 3, by norm_num, by norm_num⟩, ⟨1, 2, by norm_num, by norm_num⟩]

/-- Region 2's worst-case retry stack: tier caps `2` and `2` at `p = 1`. -/
noncomputable abbrev region2Stack : List Layer :=
  [⟨1, 2, by norm_num, by norm_num⟩, ⟨1, 2, by norm_num, by norm_num⟩]

/-- Numeric regression: region 1's cap product is attained at the worst
case, `3·2 = 6`. -/
theorem layersAmp_region1Stack : layersAmp region1Stack = 6 := by
  norm_num [layersAmp, Layer.amp, expAttempts_def]

/-- Numeric regression: region 2's cap product is attained at the worst
case, `2·2 = 4`. -/
theorem layersAmp_region2Stack : layersAmp region2Stack = 4 := by
  norm_num [layersAmp, Layer.amp, expAttempts_def]

/-- **The mesh, certified.** Local gains read as amplified worst-case
utilizations (`γ₁ = 2·6/20 = 3/5`, `γ₂ = (3/2)·4/20 = 3/10`), failover
spill `1/5` each way: both rows contract under uniform weights
(`3/5 + 1/5 = 4/5 < 1`, `1/5 + 3/10 = 1/2 < 1`). -/
theorem mesh_certified : Certificate !![3/5, 1/5; 1/5, 3/10] :=
  certificate_of_two (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_pos one_pos (by norm_num) (by norm_num)

/-- **Fixed-fraction failover, blocked.** Spilling a fixed `3/5` of load
each way — ignoring the target's headroom — puts the spill product `9/25`
over the margin product `7/25`: no positive weight vector certifies the
mesh (`spill_floor_blocks`). Failover policy must attenuate with the
target's remaining margin. -/
theorem mesh_fixed_fraction_blocked : ¬Certificate !![3/5, 3/5; 3/5, 3/10] :=
  spill_floor_blocks (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Overload
