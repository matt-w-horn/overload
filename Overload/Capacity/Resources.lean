module

public import Overload.Basic -- shake: keep
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Basic
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
# Multi-resource limits: hops, slots, bandwidth

The single scalar bottleneck is this library's default frame. A real
request path consumes a *vector* of resources — issue slots, memory on
intermediate hops, bandwidth, bottleneck service — and retry amplification
multiplies demand on every hop it crosses. This module is the arithmetic of
which resource binds.

* `vector_goodput_bound` — per-resource capacity bound.
* `hop_amplification_bound` — the asymmetry that matters: every *attempt*
  costs `r k` at hop `k`, while only the accepted attempt costs `s` at the
  bottom. Hops see the full amplification `A`. The bottom sees accepted
  work only.
* `binding_shift` — the iff: past the computable threshold
  `(C k · s)/(Cbot · r k)`, amplification makes hop `k` bind *before* the
  "real" bottleneck. Retry storms starve shallow resources first, so a
  configuration audit must cover every hop, not just the bottom.

Statements are per-resource (`∀ k`-shaped) on plain ℝ with explicit
hypotheses. Nothing here needs the equilibrium machinery. Conversely, a
per-resource `ClosedLoop` is just a different `(g, C)` denomination (see
`coupledLoop`'s docstring in `Overload/Stack/CoupledStack.lean`). A
componentwise vector `CongestedEq` is deliberately not attempted here —
per-resource scalar inequalities are the honest current form.
-/

@[expose] public section

namespace Overload

/-- Per-resource capacity bound: sustained goodput `G` with per-unit cost
`r k` at resource `k` is limited by that resource alone, whatever the other
resources allow. -/
theorem vector_goodput_bound {K : ℕ} {G : ℝ} {r C : Fin K → ℝ} (k : Fin K)
    (hr : 0 < r k) (h : G * r k ≤ C k) : G ≤ C k / r k := by
  rw [le_div_iff₀ hr]
  exact h

/-- **Hops see the full amplification.** With offered rate `lam`,
amplification `A`, and per-attempt cost `r k` at hop `k`, feasibility at
the hop bounds the sustainable offered rate by `C k / (A · r k)` — the
hop's capacity divided by the *amplified* per-request demand. (The bottom,
which serves only the accepted attempt, is bounded by `Cbot / s`
independently of `A`.) -/
theorem hop_amplification_bound {K : ℕ} {lam A : ℝ} {r C : Fin K → ℝ}
    (k : Fin K) (hr : 0 < r k) (hA : 0 < A)
    (hhop : lam * A * r k ≤ C k) : lam ≤ C k / (A * r k) := by
  rw [le_div_iff₀ (mul_pos hA hr), ← mul_assoc]
  exact hhop

/-- **The binding resource shifts with amplification** — hop `k` binds
strictly before the bottom exactly when the amplification exceeds the
provisioning ratio `(C k · s)/(Cbot · r k)`. Below that threshold the
bottom binds; above it, the retry storm starves the shallow resource
first. -/
theorem binding_shift {A s Cbot rk Ck : ℝ} (hr : 0 < rk) (hs : 0 < s)
    (hA : 0 < A) (hCbot : 0 < Cbot) :
    Ck / (A * rk) < Cbot / s ↔ Ck * s / (Cbot * rk) < A := by
  rw [div_lt_div_iff₀ (mul_pos hA hr) hs, div_lt_iff₀ (mul_pos hCbot hr)]
  constructor <;> intro h <;> linarith

/-- Numeric regression on the threshold: `binding_shift` at `A = 5` for a hop
provisioned 4× the bottom (4000 vs 1000, unit costs). Both sides are closed
numerals here; the *exactly when* reading is `binding_shift`'s. -/
theorem binding_shift_at_amp_five :
    ((4000 : ℝ) / (5 * 1) < 1000 / 1) ↔ ((4000 : ℝ) * 1 / (1000 * 1) < 5) :=
  binding_shift (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Numeric regression, the threshold crossed: at `A = 5` the hop caps the
system at 800 while the bottom still allows 1000. -/
theorem hop_binds_at_amp_five : (4000 : ℝ) / (5 * 1) < 1000 / 1 := by norm_num

/-- Numeric regression at the no-amplification endpoint, the other side of
`hop_binds_at_amp_five`: with the same provisioning and `A = 1`, the bottom's
`1000` is the binding limit. The inequality is immediate; what the theorem
pins is the `A · rk` shape at `A = 1`. -/
theorem bottom_binds_at_amp_one : (1000 : ℝ) / 1 ≤ 4000 / (1 * 1) := by
  norm_num

/-- Numeric regression on the per-resource bound at those numbers: goodput
`800` costs `1` unit at the bottom, leaving its capacity `1000` slack, and `5`
units at the hop, where capacity `4000` binds exactly. -/
theorem vector_goodput_bound_at_hop :
    (800 : ℝ) ≤ ![(1000 : ℝ), 4000] 0 / ![(1 : ℝ), 5] 0 ∧
      (800 : ℝ) ≤ ![(1000 : ℝ), 4000] 1 / ![(1 : ℝ), 5] 1 :=
  ⟨vector_goodput_bound 0 (by norm_num) (by norm_num),
    vector_goodput_bound 1 (by norm_num) (by norm_num)⟩

end Overload
