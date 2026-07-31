module

public import Overload.Basic -- shake: keep
public import Overload.Retry.Amplification
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
# The attempt-count distribution as a Mathlib `PMF`

`expAttempts` is *defined* as the finite geometric sum — total,
hypothesis-free, and what every closed loop consumes. This file certifies
that the definition is a genuine expectation: on `0 ≤ p ≤ 1` the
`attemptWeight` masses form a probability mass function on `Fin n`
(Mathlib's `PMF`), and the Bochner integral of the attempt count against its
measure is exactly `expAttempts p n`. Nothing downstream consumes this file;
it is the bridge for readers arriving from the stochastic side.

* `attemptDist` — the truncated-geometric attempt count as a `PMF (Fin n)`;
  outcome `j` reads "the final attempt is number `j + 1`".
* `attemptDist_apply` — the mass function is `attemptWeight`, on the nose.
* `integral_attemptDist` — **`expAttempts` is an expectation**:
  `∫ j, (j + 1) d(attemptDist) = expAttempts p n`.
-/

@[expose] public section

namespace Overload

/-- On `0 ≤ p ≤ 1` every attempt weight is nonnegative (each branch is a
product of nonnegatives). Consumed by the `PMF` construction. -/
theorem attemptWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n j : ℕ) :
    0 ≤ attemptWeight p n j := by
  unfold attemptWeight
  split
  · exact mul_nonneg (pow_nonneg hp0 j) (by linarith)
  · split
    · exact pow_nonneg hp0 j
    · exact le_rfl

/-- The truncated-geometric attempt count as a probability mass function on
`Fin n`: mass `attemptWeight p n j` on the outcome "the request's final
attempt is number `j + 1`". Normalization is `sum_attemptWeight`. -/
noncomputable def attemptDist (p : ℝ) {n : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ n) : PMF (Fin n) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (attemptWeight p n j)) (by
    rw [Fin.sum_univ_eq_sum_range fun j => ENNReal.ofReal (attemptWeight p n j),
      ← ENNReal.ofReal_sum_of_nonneg fun j _ => attemptWeight_nonneg hp0 hp1 n j,
      sum_attemptWeight p hn, ENNReal.ofReal_one])

/-- The mass function of `attemptDist` is `attemptWeight`, definitionally. -/
theorem attemptDist_apply (p : ℝ) {n : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ n) (j : Fin n) :
    attemptDist p hp0 hp1 hn j = ENNReal.ofReal (attemptWeight p n j) := rfl

/-- **`expAttempts` is an expectation.** The Bochner integral of the attempt
count `j ↦ j + 1` against the attempt distribution's measure is the
truncated-geometric mean the whole library consumes — the modeling
definition and the stochastic reading agree. -/
theorem integral_attemptDist (p : ℝ) {n : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ n) :
    ∫ j, ((j : ℝ) + 1) ∂((attemptDist p hp0 hp1 hn).toMeasure)
      = expAttempts p n := by
  rw [PMF.integral_eq_sum]
  calc ∑ j : Fin n, ((attemptDist p hp0 hp1 hn) j).toReal • ((j : ℝ) + 1)
      = ∑ j : Fin n, ((j : ℝ) + 1) * attemptWeight p n j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [attemptDist_apply, smul_eq_mul,
          ENNReal.toReal_ofReal (attemptWeight_nonneg hp0 hp1 n j), mul_comm]
    _ = ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * attemptWeight p n j :=
        Fin.sum_univ_eq_sum_range (fun j => ((j : ℝ) + 1) * attemptWeight p n j) n
    _ = expAttempts p n := sum_mul_attemptWeight p hn

/-- Numeric regression on the expectation: at `p = 1/2`, `n = 3` the
integral is `7/4`, matching `expAttempts (1/2) 3 = 7/4`. -/
theorem integral_attemptDist_half_three :
    ∫ j, ((j : ℝ) + 1)
      ∂((attemptDist (1/2 : ℝ) (n := 3) (by norm_num) (by norm_num)
        (by norm_num)).toMeasure) = 7/4 := by
  rw [integral_attemptDist]
  norm_num [expAttempts]

end Overload
