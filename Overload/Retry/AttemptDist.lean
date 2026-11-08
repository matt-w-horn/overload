module

public import Overload.Basic -- shake: keep
public import Overload.Retry.Amplification
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Upstream.Probability.Distributions.GeometricCensored
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
import Mathlib.Probability.ProbabilityMassFunction.Integrals
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
# The attempt-count distribution as a censored geometric measure

`expAttempts` is *defined* as the finite geometric sum — total,
hypothesis-free, and what every closed loop consumes. This file certifies
that the definition is a genuine expectation. With i.i.d. per-attempt failure
probability `p` and cap `n`, the number of failures before the final attempt
is the geometric count of failures before a success, with success probability
`1 - p`, censored at `n - 1`: mathlib's `geometricCensoredMeasure`
(`Upstream/Probability/Distributions/GeometricCensored.lean`, a copy of
mathlib PR 42381). The Bochner integral of the attempt count against that
measure is exactly `expAttempts p n`. Nothing downstream consumes this file.
It is the bridge for readers arriving from the stochastic side.

* `attemptDist` — the distribution of the final attempt's index, a measure
  on `ℕ`. Outcome `j` reads "the final attempt is number `j + 1`".
* `integral_attemptDist` — **`expAttempts` is an expectation**:
  `∫ j, (j + 1) d(attemptDist p n) = expAttempts p n`.

The masses themselves are mathlib's: `(1 - q) ^ j * q` below the cap,
the whole tail `(1 - q) ^ (n - 1)` at it, and `0` above it, for success
probability `q = 1 - p` (`geometricCensoredMeasure_singleton_of_lt`,
`geometricCensoredMeasure_singleton_self`,
`geometricCensoredMeasure_singleton_of_gt`). The mean computation is
mathlib's `sum_range_mul_geometric_add`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Overload

/-- The distribution of the final attempt's index (the attempt count minus
one) under i.i.d. per-attempt failure probability `p` and attempt cap `n`, as
a measure on `ℕ`. For `p ≠ 1` it is `geometricCensoredMeasure` with success
probability `1 - p`, censored at `n - 1`. At `p = 1` every attempt fails and
the request stops at the cap, so the mass sits at `n - 1`: `Measure.dirac
(n - 1)`. That branch is explicit because mathlib's geometric measure at
success probability `0` is the junk value `Measure.dirac 0`. The success
probability is `Set.projIcc 0 1 zero_le_one (1 - p)`, which equals `1 - p` on
`0 ≤ p ≤ 1`; outside that range it is clamped into `[0, 1]`, a junk value the
theorems exclude by hypothesis. -/
noncomputable def attemptDist (p : ℝ) (n : ℕ) : Measure ℕ :=
  if p = 1 then Measure.dirac (n - 1)
  else geometricCensoredMeasure (Set.projIcc 0 1 zero_le_one (1 - p)) (n - 1)

/-- **`expAttempts` is an expectation.** For `0 ≤ p ≤ 1` and `1 ≤ n`, the
Bochner integral of the attempt count `j ↦ j + 1` against `attemptDist p n`
is the truncated-geometric mean the whole library consumes — the modeling
definition and the stochastic reading agree. -/
theorem integral_attemptDist {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ∫ j, ((j : ℝ) + 1) ∂(attemptDist p n) = expAttempts p n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [attemptDist, Nat.add_sub_cancel]
  split_ifs with h1
  · subst h1
    rw [integral_dirac, expAttempts_def]
    simp
  · have hp : p < 1 := lt_of_le_of_ne hp1 h1
    set q : unitInterval := Set.projIcc 0 1 zero_le_one (1 - p) with hq_def
    have hq : (q : ℝ) = 1 - p := by
      rw [hq_def, Set.projIcc_of_mem _ ⟨by linarith, by linarith⟩]
    have hq0 : q ≠ 0 := fun h => by
      have := congrArg Subtype.val h
      simp only [Set.Icc.coe_zero] at this
      linarith
    have hint : Integrable (fun j : ℕ => (j : ℝ) + 1) (geometricCensoredMeasure q m) := by
      refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable ((m : ℝ) + 1) ?_
      rw [ae_iff, geometricCensoredMeasure_apply]
      convert measure_empty (μ := geometricMeasure q)
      ext k
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [Real.norm_of_nonneg (by positivity)]
      exact_mod_cast Nat.succ_le_succ (min_le_right k m)
    rw [integral_countable hint, tsum_eq_sum (s := Finset.range (m + 1)) fun j hj => by
      rw [measureReal_def, geometricCensoredMeasure_singleton_of_gt
        (by simpa using hj), ENNReal.toReal_zero, zero_smul]]
    have hpos : ∀ j : ℕ, 0 ≤ (1 - (q : ℝ)) ^ j := fun j => pow_nonneg (by linarith) j
    rw [Finset.sum_range_succ, measureReal_def, geometricCensoredMeasure_singleton_self hq0,
      ENNReal.toReal_ofReal (hpos m), Finset.sum_congr rfl fun j hj => by
        rw [measureReal_def, geometricCensoredMeasure_singleton_of_lt hq0 (Finset.mem_range.mp hj),
          ENNReal.toReal_ofReal (mul_nonneg (hpos j) q.2.1)]]
    simp only [smul_eq_mul, hq, sub_sub_cancel]
    have hexp : ∀ k : ℕ, expAttempts p (k + 1) = 1 + ∑ i ∈ Finset.Icc 1 k, p ^ i := by
      intro k
      induction k with
      | zero => simp [expAttempts]
      | succ k ih =>
        rw [expAttempts_succ, ih, Finset.sum_Icc_succ_top (by omega)]
        ring
    have hS := sum_range_mul_geometric_add p m
    have hG := one_sub_mul_expAttempts p m
    rw [expAttempts_def, Finset.mul_sum] at hG
    rw [hexp, ← hS]
    have hsplit : ∑ j ∈ Finset.range m, p ^ j * (1 - p) * ((j : ℝ) + 1)
        = ∑ j ∈ Finset.range m, (j : ℝ) * (p ^ j * (1 - p))
          + ∑ j ∈ Finset.range m, (1 - p) * p ^ j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, hG]
    ring

/-- Numeric regression on the expectation: at `p = 1/2`, `n = 3` the
integral is `7/4`, matching `expAttempts (1/2) 3 = 7/4`. -/
theorem integral_attemptDist_half_three :
    ∫ j, ((j : ℝ) + 1) ∂(attemptDist (1/2 : ℝ) 3) = 7/4 := by
  rw [integral_attemptDist (by norm_num) (by norm_num) (by norm_num)]
  norm_num [expAttempts]

end Overload
