module

public import Overload.Basic -- shake: keep
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Field.GeomSum
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
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Amplification: the truncated-geometric attempt count

One retry mechanism, i.i.d. per-attempt failure probability `p`, attempt cap
`n`. The number of attempts `K` is truncated geometric, and its mean — the
*amplification* of the mechanism — is the finite geometric sum
`E[K] = ∑_{k<n} pᵏ`, with closed form `(1 - pⁿ)/(1 - p)` away from `p = 1`.

Design note: `expAttempts` is *defined* as the sum, so it is total. The
closed-form quotient is Mathlib's `geom_sum_eq` (hypothesis `p ≠ 1`, oriented
`(pⁿ - 1)/(p - 1)` upstream), reached through `expAttempts_def`.
The distributional facts (`sum_attemptWeight`, `sum_mul_attemptWeight`) are
ring identities — true for every real `p` — because the weights telescope.
Probability hypotheses (`0 ≤ p ≤ 1`) enter only for nonnegativity, bounds, and
monotonicity.
-/

@[expose] public section

namespace Overload

/-- Expected number of attempts for one request under i.i.d. per-attempt
failure probability `p` and attempt cap `n` (truncated geometric mean),
defined as the finite geometric sum `∑_{k<n} pᵏ`. -/
def expAttempts (p : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, p ^ k

/-- `expAttempts` unfolded to the finite geometric sum it is defined as, so
call sites can reach Mathlib's `geom_sum_*` family. Deliberately not `@[simp]`:
a simp registration unfolds `expAttempts` library-wide. Name it at the site
instead. -/
theorem expAttempts_def (p : ℝ) (n : ℕ) :
    expAttempts p n = ∑ k ∈ Finset.range n, p ^ k := rfl

/-- Raising the cap by one adds the next geometric term `pⁿ` (Mathlib's
`Finset.sum_range_succ`, restated on `expAttempts`). -/
theorem expAttempts_succ (p : ℝ) (n : ℕ) :
    expAttempts p (n + 1) = expAttempts p n + p ^ n :=
  Finset.sum_range_succ _ _

/-- `(1 - p) · E[K] = 1 - pⁿ`, as a ring identity with no hypotheses on `p`
(Mathlib's `mul_neg_geom_sum`, restated on `expAttempts`). -/
theorem one_sub_mul_expAttempts (p : ℝ) (n : ℕ) :
    (1 - p) * expAttempts p n = 1 - p ^ n :=
  mul_neg_geom_sum p n

/-!
## The attempt-count distribution

`attemptWeight p n j` is `P(K = j + 1)`, indexed by the number `j` of failed
attempts before the final one. The mass is `pʲ(1-p)` while another attempt
remains (`j + 1 < n`), `p^{n-1}` at the cap (the request stops there
regardless of the final outcome), and `0` outside the support.
Indexing by `j` rather than `k = j+1`
avoids ℕ-subtraction throughout.
-/

/-- `P(K = j + 1)` for the truncated-geometric attempt count. -/
def attemptWeight (p : ℝ) (n j : ℕ) : ℝ :=
  if j + 1 < n then p ^ j * (1 - p) else if j + 1 = n then p ^ j else 0

/-- Below the cap the weight is the geometric step `pʲ(1-p)`. -/
theorem attemptWeight_of_lt {p : ℝ} {n j : ℕ} (h : j + 1 < n) :
    attemptWeight p n j = p ^ j * (1 - p) := by
  unfold attemptWeight
  rw [if_pos h]

/-- At the cap the final attempt absorbs the whole tail: `p^{n-1}`. -/
theorem attemptWeight_at_cap {p : ℝ} {j : ℕ} :
    attemptWeight p (j + 1) j = p ^ j := by
  unfold attemptWeight
  rw [if_neg (by omega), if_pos rfl]

/-- Outside the support the weight is zero — the definition's third branch,
disclosed in the module docstring, as a kernel-checked fact. -/
theorem attemptWeight_of_cap_lt {p : ℝ} {n j : ℕ} (h : n < j + 1) :
    attemptWeight p n j = 0 := by
  unfold attemptWeight
  rw [if_neg (by omega), if_neg (by omega)]

/-- Pin of the off-support branch: attempt `6` (index `5`) carries no mass
under a cap of `2`, at a failure probability that is otherwise
unremarkable. -/
theorem attemptWeight_of_cap_lt_pin : attemptWeight (1 / 2 : ℝ) 2 5 = 0 :=
  attemptWeight_of_cap_lt (by norm_num)

/-- The weights sum to `1`: a ring identity (telescoping), no `[0,1]`
hypotheses needed. -/
theorem sum_attemptWeight (p : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, attemptWeight p n j = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  rw [Finset.sum_range_succ]
  have hstep : ∀ j ∈ Finset.range m,
      attemptWeight p (m + 1) j = p ^ j * (1 - p) := fun j hj =>
    attemptWeight_of_lt (Nat.succ_lt_succ (Finset.mem_range.mp hj))
  rw [attemptWeight_at_cap, Finset.sum_congr rfl hstep, ← Finset.sum_mul]
  have h := one_sub_mul_expAttempts p m
  unfold expAttempts at h
  linear_combination h

/-- The mean of the attempt-count distribution is `expAttempts`:
`∑ (j+1) · P(K = j+1) = E[K]`. Again a ring identity. -/
theorem sum_mul_attemptWeight (p : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, ((j : ℝ) + 1) * attemptWeight p n j
      = expAttempts p n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  clear hn
  induction m with
  | zero => norm_num [attemptWeight, expAttempts]
  | succ m ih =>
    -- rewrite both the goal's sum and `ih`'s sum into the same shape
    have hstep : ∀ j ∈ Finset.range (m + 1),
        ((j : ℝ) + 1) * attemptWeight p (m + 2) j
          = ((j : ℝ) + 1) * (p ^ j * (1 - p)) := fun j hj => by
      rw [attemptWeight_of_lt (by have := Finset.mem_range.mp hj; omega)]
    have hstep' : ∀ j ∈ Finset.range m,
        ((j : ℝ) + 1) * attemptWeight p (m + 1) j
          = ((j : ℝ) + 1) * (p ^ j * (1 - p)) := fun j hj => by
      rw [attemptWeight_of_lt (by have := Finset.mem_range.mp hj; omega)]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hstep, attemptWeight_at_cap,
      Finset.sum_range_succ, expAttempts_succ, expAttempts_succ]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hstep', attemptWeight_at_cap,
      expAttempts_succ] at ih
    push_cast
    linear_combination ih

/-!
## Bounds, monotonicity, and the `p → 1` limit
-/

/-- Amplification is nonnegative once `0 ≤ p`: each term of the geometric
sum is. -/
theorem expAttempts_nonneg {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ expAttempts p n :=
  Finset.sum_nonneg fun k _ => pow_nonneg hp k

/-- Amplification is at least `1` once a first attempt exists. -/
theorem one_le_expAttempts {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ expAttempts p n := by
  simpa [expAttempts] using
    Finset.single_le_sum (f := fun k => p ^ k)
      (fun k _ => pow_nonneg hp k) (Finset.mem_range.mpr hn)

/-- Amplification never exceeds the cap. -/
theorem expAttempts_le_cap {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    expAttempts p n ≤ n := by
  calc expAttempts p n ≤ ∑ _k ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun k _ => pow_le_one₀ hp0 hp1
    _ = n := by simp

/-- Amplification is monotone in the failure probability. -/
theorem expAttempts_mono_left {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (n : ℕ) :
    expAttempts p n ≤ expAttempts q n :=
  Finset.sum_le_sum fun k _ => pow_le_pow_left₀ hp hpq k

/-- Amplification is monotone in the cap. -/
theorem expAttempts_mono_right {p : ℝ} (hp : 0 ≤ p) {m n : ℕ} (hmn : m ≤ n) :
    expAttempts p m ≤ expAttempts p n :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (fun _k hk => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) hmn))
    fun k _ _ => pow_nonneg hp k

/-- At `p = 0` nothing retries: `E[K] = 1` (for any positive cap). Mathlib's
`zero_geom_sum` is the same fact under an `ite` on `n = 0`; the hypothesis
`1 ≤ n` is the adapted form every call site here passes positionally. -/
theorem expAttempts_at_zero {n : ℕ} (hn : 1 ≤ n) : expAttempts 0 n = 1 := by
  rw [expAttempts_def, zero_geom_sum, if_neg (Nat.one_le_iff_ne_zero.mp hn)]

/-- First-order gain, lower: with at least two attempts allowed, every unit
of failure probability adds at least itself to the amplification —
`1 + p ≤ E[K]`. -/
theorem one_add_le_expAttempts {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 2 ≤ n) :
    1 + p ≤ expAttempts p n :=
  calc 1 + p = expAttempts p 2 := by rw [expAttempts_def, geom_sum_two]; ring
    _ ≤ expAttempts p n := expAttempts_mono_right hp hn

/-- First-order gain, upper: `E[K] ≤ 1 + (n-1)·p` on `[0,1]`. Together with
`one_add_le_expAttempts` this is the `E[K] ≈ 1 + Σ p` loop-gain
estimate as a two-sided sandwich. -/
theorem expAttempts_le_one_add_mul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ n : ℕ, expAttempts p n ≤ 1 + (n - 1 : ℝ) * p := by
  intro n
  cases n with
  | zero =>
    simp only [expAttempts_def, geom_sum_zero]
    push_cast
    linarith
  | succ n =>
    rw [expAttempts, Finset.sum_range_succ', pow_zero]
    have h : ∑ k ∈ Finset.range n, p ^ (k + 1) ≤ (n : ℝ) * p := by
      simpa using Finset.sum_le_card_nsmul (Finset.range n)
        (fun k => p ^ (k + 1)) p fun k _ =>
          pow_le_of_le_one hp0 hp1 k.succ_ne_zero
    push_cast
    linarith

/-- Pin of the first-order upper bound at `p = 1/2`, cap `3`, where the
linear estimate `1 + (n−1)·p` reads `2`. -/
theorem expAttempts_le_one_add_mul_pin : expAttempts (1 / 2 : ℝ) 3 ≤ 2 :=
  (expAttempts_le_one_add_mul (by norm_num) (by norm_num) 3).trans (by norm_num)

/-- The geometric tail bound `E[K] ≤ 1/(1-p)`, uniform in the cap. -/
theorem expAttempts_le_geom_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (n : ℕ) :
    expAttempts p n ≤ 1 / (1 - p) := by
  simpa [expAttempts, ← Finset.range_eq_Ico] using
    geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hp0 hp1

/-- **The geometric bound is attained**: as the cap grows without bound,
amplification converges to `(1-p)⁻¹` for `0 ≤ p < 1`. Together with
`expAttempts_le_geom_bound` this makes `1/(1-p)` the *least* uniform bound
over caps — the design number is approached, not merely respected. -/
theorem tendsto_expAttempts_geom_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Filter.Tendsto (expAttempts p) Filter.atTop (nhds (1 - p)⁻¹) :=
  Filter.Tendsto.congr (fun _ => rfl)
    (hasSum_geometric_of_lt_one hp0 hp1).tendsto_sum_nat

/-- Pin of the convergence at `p = 1/2`: raising the cap drives amplification
to `2` — with `expAttempts_le_geom_bound`, the least uniform bound there
rather than a loose one. -/
theorem tendsto_expAttempts_geom_bound_pin :
    Filter.Tendsto (expAttempts (1 / 2 : ℝ)) Filter.atTop (nhds 2) := by
  have h := tendsto_expAttempts_geom_bound (p := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)
  rwa [show ((1 : ℝ) - 1 / 2)⁻¹ = 2 by norm_num] at h

end Overload
