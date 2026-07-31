module

public import Overload.Basic -- shake: keep
public import Overload.Retry.Amplification
public import Overload.Capacity.Conservation
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

/-!
# The plateau theorem: no waste, no cliff

The uniform-loss closed loop: heterogeneous request classes share a
bottleneck of capacity `C`; at loss level `p` every attempt is accepted with
probability `1 - p`; each class `j` offers `lam j` requests per unit time and
retries to its cap `cap j`.

**Plateau theorem** (`plateau`): at *any* equilibrium of this loop, goodput is
exactly `min (∑ lam) C` — independent of every cap and (backoff never enters
the model) of every backoff schedule. Retries at a work-conserving bottleneck
with zero-cost rejection and always-useful processing cannot create a goodput
cliff. Contrapositive (`cliff_implies_waste`): any observed down-slope of
goodput under overload is a statement about a *waste channel* (duplicates,
post-abandonment work, stale-first queueing, costly rejection, failed
cancellation — see `Overload/Capacity/Conservation.lean`), not about retries
per se.
`cliff_implies_wasted` is the bridge that states that conclusion in the
accounting's own units, as strictly positive `wasted` work.

`congested_exists` shows the congested equilibrium is real, not vacuous: for
any overload `∑ lam > C` a loss level `p ∈ (0,1)` balancing the loop exists.
`uniform_congested_closedForm` gives the single-class equilibrium in closed
form, `p = (1 - C/λ)^{1/n}`.
-/

@[expose] public section

namespace Overload

variable {ι : Type*} {s : Finset ι} {lam : ι → ℝ} {cap : ι → ℕ} {C : ℝ}

/-- Total attempt rate at uniform loss `p`: every class amplifies by its
truncated-geometric mean. -/
def attemptRate (s : Finset ι) (lam : ι → ℝ) (cap : ι → ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ s, lam j * expAttempts p (cap j)

/-- Goodput at uniform loss `p`: the rate of requests that succeed within
their cap (`1 - p^{cap j}` each). -/
def goodput (s : Finset ι) (lam : ι → ℝ) (cap : ι → ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ s, lam j * (1 - p ^ cap j)

/-- Uniform-loss equilibrium: either no loss and the offered attempts fit
under capacity, or a genuine loss level at which accepted attempts exactly
exhaust capacity. -/
def UniformLossEq (s : Finset ι) (lam : ι → ℝ) (cap : ι → ℕ) (C p : ℝ) :
    Prop :=
  (p = 0 ∧ attemptRate s lam cap 0 ≤ C) ∨
  (0 < p ∧ p < 1 ∧ (1 - p) * attemptRate s lam cap p = C)

/-- The accounting identity behind everything: goodput is the accepted-attempt
rate, `G(p) = (1-p) · Λ(p)`, pointwise from `(1-p)·E[K] = 1 - pⁿ`. -/
theorem goodput_eq_one_sub_mul (s : Finset ι) (lam : ι → ℝ) (cap : ι → ℕ)
    (p : ℝ) : goodput s lam cap p = (1 - p) * attemptRate s lam cap p := by
  unfold goodput attemptRate
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_comm (1 - p) (lam j), mul_assoc,
    one_sub_mul_expAttempts]

/-- Goodput at loss level `0` is the total offered load `∑ lam`: with every
cap in `s` at least `1`, each class's summand reduces to `lam j`. -/
theorem goodput_at_zero (hcap : ∀ j ∈ s, 1 ≤ cap j) :
    goodput s lam cap 0 = ∑ j ∈ s, lam j := by
  unfold goodput
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [zero_pow (by have := hcap j hj; omega), sub_zero, mul_one]

/-- The attempt rate at loss level `0` is the total offered load `∑ lam`:
with every cap in `s` at least `1`, each class's amplification
`expAttempts 0 (cap j)` is `1`. -/
theorem attemptRate_at_zero (hcap : ∀ j ∈ s, 1 ≤ cap j) :
    attemptRate s lam cap 0 = ∑ j ∈ s, lam j := by
  unfold attemptRate
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [expAttempts_at_zero (hcap j hj), mul_one]

/-- **The plateau theorem.** At any uniform-loss equilibrium, goodput equals
`min (∑ lam) C`: independent of every retry cap, and — backoff never entering
the model — of every backoff schedule. With zero-cost rejection and
always-useful processing, retries cannot dent throughput. -/
theorem plateau (hcap : ∀ j ∈ s, 1 ≤ cap j) (hlam : ∀ j ∈ s, 0 ≤ lam j)
    {p : ℝ} (heq : UniformLossEq s lam cap C p) :
    goodput s lam cap p = min (∑ j ∈ s, lam j) C := by
  rcases heq with ⟨rfl, hfit⟩ | ⟨hp0, -, hbal⟩
  · rw [goodput_at_zero hcap, min_eq_left]
    rwa [attemptRate_at_zero hcap] at hfit
  · have hgC : goodput s lam cap p = C := by
      rw [goodput_eq_one_sub_mul, hbal]
    rw [hgC, min_eq_right]
    rw [← hgC]
    unfold goodput
    refine Finset.sum_le_sum fun j hj => ?_
    have h1 : 0 ≤ p ^ cap j := pow_nonneg (le_of_lt hp0) _
    linarith [mul_nonneg (hlam j hj) h1]

/-- A congested equilibrium exists when offered load exceeds positive
capacity and every cap in `s` is at least `1`: a loss level in `(0,1)`
balancing the loop, by the intermediate value theorem on the (continuous,
polynomial) goodput curve. -/
theorem congested_exists (hcap : ∀ j ∈ s, 1 ≤ cap j) (hC : 0 < C)
    (hover : C < ∑ j ∈ s, lam j) :
    ∃ p, 0 < p ∧ p < 1 ∧ (1 - p) * attemptRate s lam cap p = C := by
  have hcont : ContinuousOn (goodput s lam cap) (Set.Icc 0 1) := by
    refine Continuous.continuousOn ?_
    unfold goodput
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_const.sub (continuous_pow _))
  have h0 : goodput s lam cap 0 = ∑ j ∈ s, lam j := goodput_at_zero hcap
  have h1 : goodput s lam cap 1 = 0 := by
    unfold goodput
    simp
  have hsub := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont
  have hmem : C ∈ Set.Icc (goodput s lam cap 1) (goodput s lam cap 0) := by
    rw [h0, h1]
    exact ⟨le_of_lt hC, le_of_lt hover⟩
  obtain ⟨p, hp, hgp⟩ := hsub hmem
  have hpne0 : p ≠ 0 := by
    intro h
    rw [h, h0] at hgp
    exact absurd hgp (ne_of_gt hover)
  have hpne1 : p ≠ 1 := by
    intro h
    rw [h, h1] at hgp
    exact absurd hgp.symm (ne_of_gt hC)
  refine ⟨p, lt_of_le_of_ne hp.1 (Ne.symm hpne0), lt_of_le_of_ne hp.2 hpne1,
    ?_⟩
  rw [← goodput_eq_one_sub_mul]
  exact hgp

/-- Pin of the existence leg on one class: offered load `4` against capacity
`3` at cap `2`, where the intermediate value theorem delivers a loss level
strictly inside `(0, 1)`. -/
theorem congested_exists_pin :
    ∃ p, 0 < p ∧ p < 1 ∧
      (1 - p) * attemptRate (Finset.univ : Finset (Fin 1)) (fun _ => 4)
        (fun _ => 2) p = 3 :=
  congested_exists (fun _ _ => by norm_num) (by norm_num) (by norm_num)

/-- Single class, closed form: for `C < λ` the congested loss level is
exactly `p = (1 - C/λ)^{1/n}`, and goodput there is exactly `C` — whatever
the cap. The plateau, made computable. -/
theorem uniform_congested_closedForm {lam C : ℝ} {n : ℕ} (hC : 0 < C)
    (hover : C < lam) (hn : n ≠ 0) :
    0 < (1 - C / lam) ^ ((n : ℝ)⁻¹) ∧
    (1 - C / lam) ^ ((n : ℝ)⁻¹) < 1 ∧
    lam * (1 - ((1 - C / lam) ^ ((n : ℝ)⁻¹)) ^ n) = C := by
  have hlam : 0 < lam := lt_trans hC hover
  have hbase0 : 0 < 1 - C / lam := by
    rw [sub_pos, div_lt_one hlam]
    exact hover
  have hbase1 : 1 - C / lam < 1 := by
    have h : 0 < C / lam := div_pos hC hlam
    linarith
  have hinv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  refine ⟨Real.rpow_pos_of_pos hbase0 _,
    Real.rpow_lt_one (le_of_lt hbase0) hbase1 hinv, ?_⟩
  have hpn : ((1 - C / lam) ^ ((n : ℝ)⁻¹)) ^ n = 1 - C / lam :=
    Real.rpow_inv_natCast_pow (le_of_lt hbase0) hn
  rw [hpn]
  field_simp
  ring

/-- Pin of the closed form at one class: load `4` against capacity `3` at cap
`2` puts the congested loss level strictly inside `(0, 1)`, and goodput there
is exactly the capacity `3`. -/
theorem uniform_congested_closedForm_pin :
    0 < (1 - 3 / 4 : ℝ) ^ (((2 : ℕ) : ℝ)⁻¹) ∧
    (1 - 3 / 4 : ℝ) ^ (((2 : ℕ) : ℝ)⁻¹) < 1 ∧
    (4 : ℝ) * (1 - ((1 - 3 / 4 : ℝ) ^ (((2 : ℕ) : ℝ)⁻¹)) ^ (2 : ℕ)) = 3 :=
  uniform_congested_closedForm (by norm_num) (by norm_num) (by norm_num)

/-- **Cliff ⟹ waste.** If waste-discounted goodput falls below the plateau,
the discount fraction is strictly positive.

The immediacy is the content and is disclosed here rather than dressed up:
`plateau` already pins the loop's goodput to `min(∑λ, C)` exactly, so the
discount factor `w` is the *only* place a measured shortfall can live, and
the hypothesis is a rearrangement of `0 < w` once the plateau is applied. At
a fully instantiated accounting the hypothesis therefore reduces to the
conclusion verbatim (`borg_cliff_needs_waste`). What the theorem rules out
is the alternative explanation — that retries or caps moved the plateau —
not the identification of which channel `w` came from. `w` is a free
parameter here; `cliff_implies_wasted` is the version that ties it to an
`Accounting`'s `wasted` field, and `Conservation.lean` names the five
channels that field aggregates. -/
theorem cliff_implies_waste (hcap : ∀ j ∈ s, 1 ≤ cap j)
    (hlam : ∀ j ∈ s, 0 ≤ lam j) {p w : ℝ} (hw : 0 ≤ w)
    (heq : UniformLossEq s lam cap C p)
    (hcliff : (1 - w) * goodput s lam cap p < min (∑ j ∈ s, lam j) C) :
    0 < w := by
  rcases hw.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, sub_zero, one_mul, plateau hcap hlam heq] at hcliff
    exact lt_irrefl _ hcliff

/-- **Cliff ⟹ wasted work, through the accounting.** The bridge that makes
the discount fraction of `cliff_implies_waste` a named quantity: if `w` is
the waste fraction of an actual work accounting over the same bottleneck
(`W = w·C·T`, the identity `Conservation.goodput_le_of_waste` runs on), then
a cliff forces `0 < W` — strictly positive *wasted work*, in work units, in
a field whose five constituent channels are each separately measurable. The
attribution stops there: the accounting says the work was destroyed, not
which channel destroyed it. -/
theorem cliff_implies_wasted (A : Accounting) {p w : ℝ} (hw : 0 ≤ w)
    (hwaste : A.wasted = w * (A.capacity * A.time))
    (hcap : ∀ j ∈ s, 1 ≤ cap j) (hlam : ∀ j ∈ s, 0 ≤ lam j)
    (heq : UniformLossEq s lam cap C p)
    (hcliff : (1 - w) * goodput s lam cap p < min (∑ j ∈ s, lam j) C) :
    0 < A.wasted := by
  rw [hwaste]
  exact mul_pos (cliff_implies_waste hcap hlam hw heq hcliff)
    (mul_pos A.capacity_pos A.time_pos)

/-- Numeric regression: `E[K]` at `p = 1/2`, cap `3` is
`1 + 1/2 + 1/4 = 7/4`. -/
theorem expAttempts_half_three_eq : expAttempts (1 / 2 : ℝ) 3 = 7 / 4 := by
  norm_num [expAttempts, Finset.sum_range_succ]

end Overload
