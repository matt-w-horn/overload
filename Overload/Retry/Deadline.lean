module

public import Overload.Basic -- shake: keep
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Overload.Retry.Amplification

/-!
# Deadline apportionment: how many attempts fit

The end-to-end deadline `D` is the request's total budget. With
per-attempt failure latencies `T j` and backoff waits `B j` (indexed from `0`),
`k` attempts are *feasible* when their latencies plus the `k - 1` interleaved
waits fit in `D`, and `neff` is the largest feasible count under the cap `n`.

Headline results:

* `neff_antitone_latency` — **the latency-ordering proposition**: slower
  failures admit (weakly) fewer attempts, for every backoff schedule.
  Amplification therefore concentrates on the *fast* tail of the
  failure-latency distribution.
* `neff_ge_of_fast` / `neff_le` — **the fast-fail/cap tension**: for any
  target attempt count below the cap there is a rejection latency cheap enough
  to admit it, and never more than the cap, which bounds the count whatever
  the latency. Cheap rejection buys attempts up to `n` and not past it. It is
  supply-side efficient and demand-side dangerous *by arithmetic*, not by
  implementation.
* `neff_slow_remaining` / `neff_le_one_of_slow` — **remaining-deadline + slow
  failure ⟹ at most one attempt** (exactly one at the boundary `T 0 = D`):
  a failure that consumes the whole budget cannot be retried. This is the
  formal half of the sustaining-mechanisms proposition's "slow congested
  failures close the fast-fail and re-arm mechanisms".
* `neff_rearmed` / `two_le_neff_rearmed` — **re-armed per-try timeouts
  re-open it**: fixed sub-deadlines admit `⌊D/τ⌋` attempts of the very same
  slow failure.
* `neff_const` — the exact constant-backoff closed form
  `min n ⌊(D+b)/(t+b)⌋`.
* `neff_linear_backoff_le` / `neff_geom_backoff_le` — the square-root and
  logarithmic deadline levers of linear and geometric backoff, as inequalities.
-/

@[expose] public section

namespace Overload

/-- Total time consumed by `k` attempts: `k` failure latencies plus the
`k - 1` interleaved backoff waits. (`Finset.range (k-1)` is empty at `k = 0`,
so the ℕ-subtraction is harmless.) -/
def totalTime (T B : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, T j + ∑ j ∈ Finset.range (k - 1), B j

/-- `k` attempts fit within deadline `D`. -/
def fitsIn (T B : ℕ → ℝ) (D : ℝ) (k : ℕ) : Prop := totalTime T B k ≤ D

open Classical in
/-- The deadline-capped attempt count: the largest `k ≤ n` whose attempts
fit in `D` (junk `0` when none fits — `Nat.findGreatest`'s fallback, per
the totality convention; the theorems supply the fitting hypothesis). -/
noncomputable def neff (T B : ℕ → ℝ) (D : ℝ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fitsIn T B D) n

variable {T T' B B' : ℕ → ℝ} {D D' t b : ℝ} {k n : ℕ}

/-- Zero attempts consume zero time. -/
@[simp] theorem totalTime_zero (T B : ℕ → ℝ) : totalTime T B 0 = 0 := by
  simp [totalTime]

/-- Zero attempts fit within any nonnegative deadline. -/
theorem fitsIn_zero (T B : ℕ → ℝ) (hD : 0 ≤ D) : fitsIn T B D 0 := by
  simp [fitsIn, hD]

/-- The cap side of the tension: `neff` never exceeds the configured cap. -/
theorem neff_le (T B : ℕ → ℝ) (D : ℝ) (n : ℕ) : neff T B D n ≤ n := by
  classical
  unfold neff
  exact Nat.findGreatest_le n

/-- Within a nonnegative deadline (`0 ≤ D`), the attempts `neff` claims
feasible really fit. -/
theorem fitsIn_neff (hD : 0 ≤ D) : fitsIn T B D (neff T B D n) := by
  classical
  unfold neff
  exact Nat.findGreatest_spec (Nat.zero_le n) (fitsIn_zero T B hD)

/-- Any feasible count within the cap is a lower bound on `neff`. -/
theorem le_neff (hk : k ≤ n) (h : fitsIn T B D k) : k ≤ neff T B D n := by
  classical
  unfold neff
  exact Nat.le_findGreatest hk h

/-!
## Monotonicity: the latency-ordering proposition and friends
-/

/-- `totalTime` is monotone in the failure latencies: pointwise-slower
failures consume at least as much time, for any backoff schedule and any
attempt count. -/
theorem totalTime_mono_T (h : ∀ j, T j ≤ T' j) (B : ℕ → ℝ) (k : ℕ) :
    totalTime T B k ≤ totalTime T' B k :=
  add_le_add (Finset.sum_le_sum fun j _ => h j) le_rfl

/-- **Latency ordering**: pointwise-slower failures
admit (weakly) fewer attempts, for any backoff schedule and any deadline.
Amplification concentrates on the fast tail. -/
theorem neff_antitone_latency (h : ∀ j, T j ≤ T' j) :
    neff T' B D n ≤ neff T B D n := by
  classical
  unfold neff
  exact Nat.findGreatest_mono_left
    (fun k hk => le_trans (totalTime_mono_T h B k) hk) n

/-!
## The constant-backoff closed form and re-armed timeouts
-/

/-- `totalTime` at constant latency `t` and constant wait `b`: `m + 1`
attempts consume `(m + 1)·t + m·b`. Stated at a successor count so the
ℕ-subtraction `(m + 1) - 1` reduces to `m`. -/
theorem totalTime_const_succ (t b : ℝ) (m : ℕ) :
    totalTime (fun _ => t) (fun _ => b) (m + 1)
      = (m + 1 : ℝ) * t + (m : ℝ) * b := by
  simp only [totalTime, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.add_sub_cancel]
  push_cast
  ring

/-- **Constant backoff, exact**: with per-attempt latency `t > 0` and
nonnegative constant wait `b`, a nonnegative deadline admits exactly
`min n ⌊(D+b)/(t+b)⌋` attempts. -/
theorem neff_const (ht : 0 < t) (hb : 0 ≤ b) (hD : 0 ≤ D) (n : ℕ) :
    neff (fun _ => t) (fun _ => b) D n = min n ⌊(D + b) / (t + b)⌋₊ := by
  have htb : 0 < t + b := by linarith
  apply le_antisymm
  · refine le_min (neff_le _ _ _ _) ?_
    rcases Nat.eq_zero_or_pos (neff (fun _ => t) (fun _ => b) D n) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have hfits := fitsIn_neff (T := fun _ => t) (B := fun _ => b) (n := n) hD
      rw [hm] at hfits
      unfold fitsIn at hfits
      rw [totalTime_const_succ] at hfits
      have hle : ((m + 1 : ℕ) : ℝ) ≤ (D + b) / (t + b) := by
        rw [le_div_iff₀ htb]
        push_cast
        linarith
      rw [hm]
      exact Nat.le_floor hle
  · rcases Nat.eq_zero_or_pos (min n ⌊(D + b) / (t + b)⌋₊) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · refine le_neff (min_le_left _ _) ?_
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hm]
      unfold fitsIn
      rw [totalTime_const_succ]
      have hfloor : m + 1 ≤ ⌊(D + b) / (t + b)⌋₊ := by omega
      have hle : ((m + 1 : ℕ) : ℝ) ≤ (D + b) / (t + b) :=
        le_trans (Nat.cast_le.mpr hfloor) (Nat.floor_le (by positivity))
      rw [le_div_iff₀ htb] at hle
      push_cast at hle ⊢
      linarith

/-- **Re-armed per-try timeout** (fixed sub-deadline `τ`, no backoff): the
deadline admits `min n ⌊D/τ⌋` attempts — of the *same* slow failure that
remaining-deadline apportionment would have stopped after one. -/
theorem neff_rearmed {τ : ℝ} (hτ : 0 < τ) (hD : 0 ≤ D) (n : ℕ) :
    neff (fun _ => τ) (fun _ => 0) D n = min n ⌊D / τ⌋₊ := by
  simpa using neff_const hτ le_rfl hD n

/-- Re-armed timeouts sustain amplification: two sub-deadlines in the budget
means at least two attempts. This is sustaining mechanism 2 in one line. -/
theorem two_le_neff_rearmed {τ : ℝ} (hτ : 0 < τ) (h2 : 2 * τ ≤ D)
    (hn : 2 ≤ n) : 2 ≤ neff (fun _ => τ) (fun _ => 0) D n := by
  have hD : 0 ≤ D := by linarith
  rw [neff_rearmed hτ hD]
  refine le_min hn (Nat.le_floor ?_)
  rw [le_div_iff₀ hτ]
  push_cast
  linarith

/-- **The whole slow regime, uniformly**: for positive latencies and
nonnegative backoffs, whenever the first failure latency meets or exceeds
the deadline (`D ≤ T 0`), at most one attempt fits — exactly one at the
boundary `T 0 = D` when an attempt is available at all
(`neff_slow_remaining`, which asks `1 ≤ n`), none when strictly slower
(`neff_eq_zero_of_strictly_slow`). Either way, a slow failure under
remaining-deadline apportionment cannot amplify. -/
theorem neff_le_one_of_slow (hT0 : D ≤ T 0) (hTpos : ∀ j, 0 < T j)
    (hB : ∀ j, 0 ≤ B j) : neff T B D n ≤ 1 := by
  classical
  by_contra h
  rw [not_le] at h
  have hfits : fitsIn T B D (neff T B D n) := by
    unfold neff at h ⊢
    exact (Nat.findGreatest_eq_iff.1 rfl).2.1 (by omega)
  unfold fitsIn totalTime at hfits
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (neff T B D n) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> (rw [Finset.mem_range]; omega)
  have hTsum : T 0 + T 1 ≤ ∑ j ∈ Finset.range (neff T B D n), T j := by
    have h01 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => le_of_lt (hTpos j))
    rwa [Finset.sum_pair (by omega : (0 : ℕ) ≠ 1)] at h01
  have hBsum : 0 ≤ ∑ j ∈ Finset.range (neff T B D n - 1), B j :=
    Finset.sum_nonneg fun j _ => hB j
  have hT1 := hTpos 1
  linarith

/-- **Remaining-deadline apportionment stops a slow failure at one attempt**:
if the first attempt consumes exactly the whole budget (`T 0 = D`), every
attempt takes positive time, backoffs are nonnegative, and at least one
attempt is available (`1 ≤ n`), exactly one attempt fits. Slow failures cannot
amplify under remaining-deadline propagation.

This is the boundary case of the semantics: `fitsIn` counts attempts that
*complete* within the budget, so a failure strictly slower than the deadline
admits zero completed attempts (the physical "one attempt was started and
abandoned" is not a completed attempt). `neff_le_one_of_slow` covers the
whole slow regime `D ≤ T 0` with the uniform bound `neff ≤ 1`. -/
theorem neff_slow_remaining (hT0 : T 0 = D) (hTpos : ∀ j, 0 < T j)
    (hB : ∀ j, 0 ≤ B j) (hn : 1 ≤ n) : neff T B D n = 1 := by
  apply le_antisymm (neff_le_one_of_slow hT0.ge hTpos hB)
  refine le_neff hn ?_
  unfold fitsIn totalTime
  rw [Finset.sum_range_one, show (1 : ℕ) - 1 = 0 from rfl,
    Finset.range_zero, Finset.sum_empty, add_zero, hT0]

/-- **Strictly slower than the deadline ⟹ no attempt completes**: for
nonnegative latencies and backoffs, when the first failure latency exceeds
the whole budget (`D < T 0`), the exact count is `0`, not merely at most
one. `fitsIn` counts attempts that *complete* within
the budget, and here none does — the sharp value inside
`neff_le_one_of_slow`'s uniform bound, whose other boundary case is
`neff_slow_remaining`'s exact `1`. -/
theorem neff_eq_zero_of_strictly_slow (hT0 : D < T 0) (hT : ∀ j, 0 ≤ T j)
    (hB : ∀ j, 0 ≤ B j) : neff T B D n = 0 := by
  classical
  by_contra hne
  have hfits : fitsIn T B D (neff T B D n) := by
    unfold neff at hne ⊢
    exact (Nat.findGreatest_eq_iff.1 rfl).2.1 hne
  have hpos : 0 < neff T B D n := Nat.pos_of_ne_zero hne
  unfold fitsIn totalTime at hfits
  have hTsum : T 0 ≤ ∑ j ∈ Finset.range (neff T B D n), T j :=
    Finset.single_le_sum (fun j _ => hT j) (Finset.mem_range.mpr hpos)
  have hBsum : 0 ≤ ∑ j ∈ Finset.range (neff T B D n - 1), B j :=
    Finset.sum_nonneg fun j _ => hB j
  linarith

/-- Pin of the strictly-slow corner: 5-second failures against a 2-second
deadline complete no attempt at all, whatever the configured cap — here
`10`. -/
theorem neff_eq_zero_of_strictly_slow_pin :
    neff (fun _ => (5 : ℝ)) (fun _ => 0) 2 10 = 0 :=
  neff_eq_zero_of_strictly_slow (by norm_num) (fun _ => by norm_num)
    (fun _ => le_rfl)

/-!
## The fast-fail side of the tension
-/

/-- Cheap attempts fit: if every failure resolves within `t` and `k·t ≤ D`,
then `k` back-to-back attempts fit in the deadline. -/
theorem fitsIn_of_cheap {t : ℝ} (hT : ∀ j, T j ≤ t) (hkt : (k : ℝ) * t ≤ D) :
    fitsIn T (fun _ => 0) D k := by
  unfold fitsIn totalTime
  simp only [Finset.sum_const_zero, add_zero]
  refine le_trans ?_ hkt
  simpa using Finset.sum_le_card_nsmul (Finset.range k) T t fun j _ => hT j

/-- **Cheap rejection realizes any target count within the cap**: for any
target attempt count `k` within the cap and any positive deadline, there is a
rejection latency `t > 0` below which every failure profile admits at least
`k` attempts. Backoff is pinned to zero here; with a nonzero schedule timing
does bound attempts (`neff_linear_backoff_le`, `neff_geom_backoff_le`), and
`neff_le` caps them at `n` regardless. -/
theorem neff_ge_of_fast (hkn : k ≤ n) (hD : 0 < D) :
    ∃ t, 0 < t ∧ ∀ T : ℕ → ℝ, (∀ j, T j ≤ t) →
      k ≤ neff T (fun _ => 0) D n := by
  refine ⟨D / (k + 1), by positivity, fun T hT => ?_⟩
  refine le_neff hkn (fitsIn_of_cheap hT ?_)
  have hk1 : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hpos : 0 ≤ D / ((k : ℝ) + 1) := by positivity
  calc (k : ℝ) * (D / ((k : ℝ) + 1))
      ≤ ((k : ℝ) + 1) * (D / ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hk1 hpos
    _ = D := by field_simp

/-- Pin of the fast-fail leg at a 10-second deadline and a cap of `20`: some
positive rejection latency admits `5` attempts. The threshold the proof
exhibits is `D/(k+1)`, so it is not vacuously small. -/
theorem neff_ge_of_fast_pin :
    ∃ t, 0 < t ∧ ∀ T : ℕ → ℝ, (∀ j, T j ≤ t) →
      5 ≤ neff T (fun _ => 0) 10 20 :=
  neff_ge_of_fast (by norm_num) (by norm_num)

/-!
## Linear and geometric backoff bounds
-/

/-- Gauss's sum in the shape the linear-backoff schedule needs: over `ℝ`, and
summing `j + 1` rather than `j`. The arithmetic is Mathlib's
`Finset.sum_range_id_mul_two`; what stays local is the cast, which is why the
statement is not simply that lemma — upstream is over `ℕ` with truncated
subtraction, and the shift to `range (m + 1)` is what avoids it. -/
theorem sum_range_add_one (m : ℕ) :
    ∑ j ∈ Finset.range m, ((j : ℝ) + 1) = m * (m + 1) / 2 := by
  have h := Finset.sum_range_id_mul_two (m + 1)
  simp only [Finset.sum_range_succ' (fun i => i) m, Nat.add_sub_cancel,
    Nat.add_zero] at h
  have hc : ((∑ j ∈ Finset.range m, (j + 1) : ℕ) : ℝ) * 2 = ((m : ℝ) + 1) * m := by
    exact_mod_cast h
  push_cast at hc
  linarith

/-- **Linear backoff is a square-root lever on the deadline**: with waits
`b, 2b, 3b, …` the attempt count is at most `1 + √(2D/b)`, whatever the
failure latencies. -/
theorem neff_linear_backoff_le (hb : 0 < b) (hT : ∀ j, 0 ≤ T j) (hD : 0 ≤ D)
    (n : ℕ) :
    (neff T (fun j => ((j : ℝ) + 1) * b) D n : ℝ)
      ≤ 1 + Real.sqrt (2 * D / b) := by
  rcases Nat.eq_zero_or_pos (neff T (fun j => ((j : ℝ) + 1) * b) D n) with
    h0 | hpos
  · rw [h0]
    have := Real.sqrt_nonneg (2 * D / b)
    push_cast
    linarith
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hfits := fitsIn_neff (T := T) (B := fun j => ((j : ℝ) + 1) * b)
      (n := n) hD
    rw [hm] at hfits
    unfold fitsIn totalTime at hfits
    have hTs : 0 ≤ ∑ j ∈ Finset.range (m + 1), T j :=
      Finset.sum_nonneg fun j _ => hT j
    have hBs : ∑ j ∈ Finset.range (m + 1 - 1), ((j : ℝ) + 1) * b
        = b * ((m : ℝ) * (m + 1) / 2) := by
      simp only [Nat.add_sub_cancel]
      rw [← Finset.sum_mul, sum_range_add_one]
      ring
    rw [hBs] at hfits
    have hkey : (m : ℝ) ^ 2 ≤ 2 * D / b := by
      rw [le_div_iff₀ hb]
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith [mul_nonneg hb.le hmnn]
    have hmle : (m : ℝ) ≤ Real.sqrt (2 * D / b) :=
      Real.le_sqrt_of_sq_le hkey
    rw [hm]
    push_cast
    linarith

/-- **Geometric backoff is a logarithmic lever on the deadline**: with waits
`b, rb, r²b, …` (ratio `r > 1`) the attempt count is at most
`1 + log_r(1 + D(r-1)/b)`, whatever the failure latencies. -/
theorem neff_geom_backoff_le {r : ℝ} (hr : 1 < r) (hb : 0 < b)
    (hT : ∀ j, 0 ≤ T j) (hD : 0 ≤ D) (n : ℕ) :
    (neff T (fun j => b * r ^ j) D n : ℝ)
      ≤ 1 + Real.logb r (1 + D * (r - 1) / b) := by
  have hX1 : (1 : ℝ) ≤ 1 + D * (r - 1) / b := by
    have h : 0 ≤ D * (r - 1) / b := by positivity
    linarith
  rcases Nat.eq_zero_or_pos (neff T (fun j => b * r ^ j) D n) with h0 | hpos
  · rw [h0]
    have := Real.logb_nonneg hr hX1
    push_cast
    linarith
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hfits := fitsIn_neff (T := T) (B := fun j => b * r ^ j) (n := n) hD
    rw [hm] at hfits
    unfold fitsIn totalTime at hfits
    have hTs : 0 ≤ ∑ j ∈ Finset.range (m + 1), T j :=
      Finset.sum_nonneg fun j _ => hT j
    have hBs : ∑ j ∈ Finset.range (m + 1 - 1), b * r ^ j
        = b * expAttempts r m := by
      simp only [Nat.add_sub_cancel]
      unfold expAttempts
      rw [Finset.mul_sum]
    rw [hBs] at hfits
    have hE : expAttempts r m ≤ D / b := by
      rw [le_div_iff₀ hb]
      linarith
    have hgeom := one_sub_mul_expAttempts r m
    have hrm : r ^ m ≤ 1 + D * (r - 1) / b := by
      have h2 : (r - 1) * expAttempts r m ≤ (r - 1) * (D / b) :=
        mul_le_mul_of_nonneg_left hE (by linarith)
      have h3 : (r - 1) * (D / b) = D * (r - 1) / b := by ring
      linarith
    have hlog : (m : ℝ) ≤ Real.logb r (1 + D * (r - 1) / b) := by
      have hpow : (0 : ℝ) < r ^ m := pow_pos (by linarith) m
      have hmono := Real.logb_le_logb_of_le hr hpow hrm
      rwa [Real.logb_pow, Real.logb_self_eq_one hr, mul_one] at hmono
    rw [hm]
    push_cast
    linarith

/-- Pin of the square-root lever: with unit linear backoff and an 8-second
deadline, at most `5` attempts fit however large the configured cap — here
`100`, twenty times the bound. -/
theorem neff_linear_backoff_le_pin :
    (neff (fun _ => (1 : ℝ)) (fun j => ((j : ℝ) + 1) * 1) 8 100 : ℝ) ≤ 5 := by
  refine (neff_linear_backoff_le one_pos (fun _ => zero_le_one)
    (by norm_num) 100).trans ?_
  rw [show (2 * 8 / 1 : ℝ) = 4 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- Pin of the logarithmic lever: doubling backoff from a 1-second base
against a 7-second deadline admits at most `4` attempts, again whatever the
configured cap — here `100`. -/
theorem neff_geom_backoff_le_pin :
    (neff (fun _ => (1 : ℝ)) (fun j => 1 * 2 ^ j) 7 100 : ℝ) ≤ 4 := by
  refine (neff_geom_backoff_le (by norm_num) one_pos (fun _ => zero_le_one)
    (by norm_num) 100).trans ?_
  rw [show (1 + 7 * ((2 : ℝ) - 1) / 1) = 2 ^ (3 : ℕ) by norm_num,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- Numeric regression: 1s attempts, no backoff, 3.5s deadline, cap `10` →
3 attempts. -/
theorem neff_unit_no_backoff_eq_three :
    neff (fun _ => (1 : ℝ)) (fun _ => 0) (7 / 2) 10 = 3 := by
  rw [neff_rearmed one_pos (by norm_num)]
  have h : ⌊(7 / 2 / 1 : ℝ)⌋₊ = 3 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [h]
  omega

/-- Pin of latency ordering against that regression: doubling every failure
latency to 2s cannot buy more than the `3` attempts the 1s profile gets at the
same 3.5s deadline. -/
theorem neff_antitone_latency_pin :
    neff (fun _ => (2 : ℝ)) (fun _ => 0) (7 / 2) 10 ≤ 3 := by
  rw [← neff_unit_no_backoff_eq_three]
  exact neff_antitone_latency (fun _ => by norm_num)

end Overload
