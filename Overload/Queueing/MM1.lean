module

public import Overload.Basic -- shake: keep
public import Overload.Loop.ClosedLoop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
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
# M/M/1 mean-value theory: the utilization law

The queueing law behind every load-coupled failure kernel in this library:
as utilization `ρ = λ/μ` approaches one, the stationary queue — and through
Little's law, delay — blows up like `1/(1-ρ)`. This is the equation behind
"the system got slow before it fell over", and the reason failure
probability couples to load at all: past the knee, any fixed timeout is
eventually crossed. Historically, this is the classical base model of
time-shared (multitasking) computer systems.

**Modeling interface, stated honestly.** No measure theory and no
Markov-chain formalism enter. "Stationary" here means exactly three proved
facts about the explicit geometric weights: they sum to one
(`hasSum_stationaryWeight`), they satisfy the birth–death balance equations
(`stationaryWeight_succ`, `detailed_balance`), and they are the **unique**
summable-to-one solution of that recurrence (`stationaryWeight_unique`).
Little's law enters as the *definition* of `meanWait` — the same interface
stance `Overload/Verification/Suite.lean` takes for PASTA. Nothing here
claims discipline-invariance, and the M/M/1 *retrial* queue's closed forms
(test 10 in `Suite.lean`) remain unformalized.

Results:

* `hasSum_stationaryWeight` / `tsum_stationaryWeight` — normalization.
* `stationaryWeight_succ` / `detailed_balance` / `global_balance` — the
  balance equations, in utilization and flow forms.
* `stationaryWeight_unique` — the balance recurrence plus normalization
  *forces* the geometric solution.
* `global_balance_iff_cutFlow_succ` / `stationaryWeight_unique_of_global_balance`
  — global balance *is* constancy of the cut flow, and summability collapses
  that constant to zero, so under the stability condition `0 ≤ λ < μ` the
  geometric form is derived from the second-order balance equations rather
  than assumed.
* `meanQueue_eq` — **`L = ρ/(1-ρ)`**, the utilization law.
* `meanQueueWaiting_eq` / `meanQueueWaiting_add_util` — `Lq = ρ²/(1-ρ)`
  and `Lq + ρ = L`.
* `meanQueue_strictMonoOn` / `tendsto_meanQueue_atTop` — the knee: strictly
  increasing in utilization, and divergent as `ρ → 1⁻`.
* `meanWait_eq` — **`W = 1/(μ-λ)`**, the delay law, through the Little
  bridge.
* `meanQueue_eq_lam_mul_meanWait` / `meanWait_eq_of_little` — that bridge
  stated: `L = λ·W` is definitional for this file's `meanWait`, and the
  delay law also follows from `L = λ·W` carried as a hypothesis on an
  externally supplied `W`.
* `mm1Loop_bistable` / `mm1Loop_two_fixedPts` / `mm1Loop_congestedEq` — the
  band on the queueing-derived kernel, and its two genuine equilibria.
-/

@[expose] public section

namespace Overload

/-- Stationary weight of queue length `n` at utilization `ρ`:
`P(N = n) = (1-ρ)·ρⁿ`. Total in `ρ`; the probability reading needs
`0 ≤ ρ < 1`, stated on the lemmas that use it. -/
def stationaryWeight (ρ : ℝ) (n : ℕ) : ℝ := (1 - ρ) * ρ ^ n

/-- Definitional unfolding at `n = 0`: the empty-queue weight is `1 - ρ`. -/
@[simp] theorem stationaryWeight_zero (ρ : ℝ) :
    stationaryWeight ρ 0 = 1 - ρ := by
  simp [stationaryWeight]

/-- For `0 ≤ ρ ≤ 1` the weights are nonnegative: both factors of
`(1-ρ)·ρⁿ` are. -/
theorem stationaryWeight_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n : ℕ) :
    0 ≤ stationaryWeight ρ n :=
  mul_nonneg (by linarith) (pow_nonneg h0 n)

/-- Detailed balance, utilization form: `π(n+1) = ρ·π(n)`, a ring identity. -/
theorem stationaryWeight_succ (ρ : ℝ) (n : ℕ) :
    stationaryWeight ρ (n + 1) = ρ * stationaryWeight ρ n := by
  unfold stationaryWeight
  ring

/-- Detailed balance, flow form: at `ρ = λ/μ` the down-flow `μ·π(n+1)`
equals the up-flow `λ·π(n)` — the birth–death cut equations of M/M/1. -/
theorem detailed_balance {lam mu : ℝ} (hmu : mu ≠ 0) (n : ℕ) :
    mu * stationaryWeight (lam / mu) (n + 1)
      = lam * stationaryWeight (lam / mu) n := by
  rw [stationaryWeight_succ]
  field_simp

/-- Global balance at interior states, from two detailed-balance cuts:
`(λ+μ)·π(n+1) = λ·π(n) + μ·π(n+2)`. -/
theorem global_balance {lam mu : ℝ} (hmu : mu ≠ 0) (n : ℕ) :
    (lam + mu) * stationaryWeight (lam / mu) (n + 1)
      = lam * stationaryWeight (lam / mu) n
        + mu * stationaryWeight (lam / mu) (n + 2) := by
  have h1 := detailed_balance (lam := lam) hmu n
  have h2 := detailed_balance (lam := lam) hmu (n + 1)
  linarith

/-- Pin of `global_balance` at `λ = 1, μ = 2, n = 0`: `3·π(1) = 1·π(0) + 2·π(2)`
over the closed-form weights (`3/4 = 1/2 + 1/4`). The recursion is a
consistency check of the closed form against an equation written in the same
file — the independent verification of `stationaryWeight` is
`stationaryWeight_unique_of_global_balance`, which quantifies over all
solutions summing to `1`, for `0 ≤ λ < μ`. -/
theorem global_balance_pin :
    (1 + 2 : ℝ) * stationaryWeight (1 / 2) 1
      = 1 * stationaryWeight (1 / 2) 0 + 2 * stationaryWeight (1 / 2) 2 :=
  global_balance (lam := 1) (mu := 2) (by norm_num) 0

/-- The stationary weights are a probability distribution. -/
theorem hasSum_stationaryWeight {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    HasSum (stationaryWeight ρ) 1 := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - ρ)
  have hne : (1 : ℝ) - ρ ≠ 0 := by linarith
  rw [mul_inv_cancel₀ hne] at h
  exact h

/-- Normalization in `tsum` form: `hasSum_stationaryWeight` read off as
`∑' n, π(n) = 1`. -/
theorem tsum_stationaryWeight {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∑' n, stationaryWeight ρ n = 1 :=
  (hasSum_stationaryWeight h0 h1).tsum_eq

/-- Pins of the distribution facts at `ρ = 1/2`, one leg per fact: the
empty-queue weight is `1/2` (`stationaryWeight_zero`), the weight at `n = 3`
is nonnegative (`stationaryWeight_nonneg`), and the weights normalize to one
(`tsum_stationaryWeight`). -/
theorem stationaryWeight_half_pin :
    stationaryWeight (1 / 2) 0 = 1 / 2 ∧
      (0 : ℝ) ≤ stationaryWeight (1 / 2) 3 ∧
      ∑' n, stationaryWeight (1 / 2 : ℝ) n = 1 :=
  ⟨by rw [stationaryWeight_zero]; norm_num,
    stationaryWeight_nonneg (by norm_num) (by norm_num) 3,
    tsum_stationaryWeight (by norm_num) (by norm_num)⟩

/-- **The balance equations force the geometric solution**: any solution of
the recurrence `f (n+1) = ρ·f n` that sums to one is `stationaryWeight ρ`.
No sign hypothesis on `f` is needed — normalization pins it. -/
theorem stationaryWeight_unique {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1)
    {f : ℕ → ℝ} (hrec : ∀ n, f (n + 1) = ρ * f n) (hsum : HasSum f 1) :
    ∀ n, f n = stationaryWeight ρ n := by
  have hpow : ∀ n, f n = f 0 * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hrec n, ih, pow_succ]; ring
  have hfun : f = fun n => f 0 * ρ ^ n := funext hpow
  rw [hfun] at hsum
  have hgeom : HasSum (fun n => f 0 * ρ ^ n) (f 0 * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one h0 h1).mul_left (f 0)
  have hne : (1 : ℝ) - ρ ≠ 0 := by linarith
  have hf0 : f 0 = 1 - ρ := (mul_inv_eq_one₀ hne).mp (hgeom.unique hsum)
  intro n
  rw [hpow n, hf0]
  rfl

/-- The net probability flow across the cut separating states `≤ n` from
states `≥ n+1`: down-flow `μ·f (n+1)` minus up-flow `λ·f n`. Detailed
balance is exactly its vanishing. -/
def cutFlow (lam mu : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ := mu * f (n + 1) - lam * f n

/-- **Global balance is cut-flow constancy.** The interior balance equation
at `n` holds precisely when the cut flow across `n+1` equals the cut flow
across `n` — a rearrangement, needing no hypotheses. This is why the
second-order birth–death recurrence pins only the *differences* of the cut
flows and leaves a one-parameter family: the constant branch. -/
theorem global_balance_iff_cutFlow_succ {lam mu : ℝ} {f : ℕ → ℝ} {n : ℕ} :
    (lam + mu) * f (n + 1) = lam * f n + mu * f (n + 2)
      ↔ cutFlow lam mu f (n + 1) = cutFlow lam mu f n := by
  unfold cutFlow
  constructor <;> intro h <;> linarith

/-- Global balance at every interior state makes the cut flow constant in
`n` (`global_balance_iff_cutFlow_succ`, iterated). -/
theorem cutFlow_const_of_global_balance {lam mu : ℝ} {f : ℕ → ℝ}
    (hbal : ∀ n, (lam + mu) * f (n + 1) = lam * f n + mu * f (n + 2))
    (n : ℕ) : cutFlow lam mu f n = cutFlow lam mu f 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [global_balance_iff_cutFlow_succ.mp (hbal n), ih]

open Filter Topology in
/-- **Summability kills the constant branch.** A summable solution of the
interior balance equations has vanishing cut flow everywhere: the flow is
constant, and its two terms tend to zero with `f`, so that constant is zero.
Detailed balance is therefore *derived* from global balance plus
summability, not assumed alongside it. -/
theorem cutFlow_eq_zero_of_summable {lam mu : ℝ} {f : ℕ → ℝ}
    (hbal : ∀ n, (lam + mu) * f (n + 1) = lam * f n + mu * f (n + 2))
    (hf : Summable f) (n : ℕ) : cutFlow lam mu f n = 0 := by
  have h0 : Tendsto f atTop (𝓝 0) := hf.tendsto_atTop_zero
  have h1 : Tendsto (fun n => f (n + 1)) atTop (𝓝 0) :=
    h0.comp (tendsto_add_atTop_nat 1)
  have hcut : Tendsto (cutFlow lam mu f) atTop (𝓝 0) := by
    change Tendsto (fun n => mu * f (n + 1) - lam * f n) atTop (𝓝 0)
    simpa using (h1.const_mul mu).sub (h0.const_mul lam)
  have hconst : cutFlow lam mu f = fun _ => cutFlow lam mu f 0 :=
    funext (cutFlow_const_of_global_balance hbal)
  rw [hconst] at hcut
  rw [cutFlow_const_of_global_balance hbal n]
  exact tendsto_nhds_unique tendsto_const_nhds hcut

/-- **Uniqueness from the balance equations themselves.** Any solution of
the interior birth–death equations `(λ+μ)·f(n+1) = λ·f n + μ·f(n+2)` that
sums to one *is* the geometric stationary distribution, under the stability
condition `0 ≤ λ < μ` and with neither detailed balance nor a sign condition
on `f` assumed. Where
`stationaryWeight_unique` starts from the first-order form and only
normalizes, this starts from the two-dimensional solution space of the
second-order recurrence: summability forces the cut flow to vanish
(`cutFlow_eq_zero_of_summable`), which *is* detailed balance, and
normalization then fixes the scale. -/
theorem stationaryWeight_unique_of_global_balance {lam mu : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam < mu) {f : ℕ → ℝ}
    (hbal : ∀ n, (lam + mu) * f (n + 1) = lam * f n + mu * f (n + 2))
    (hsum : HasSum f 1) : ∀ n, f n = stationaryWeight (lam / mu) n := by
  have hmu : 0 < mu := h0.trans_lt h1
  have hmune : mu ≠ 0 := hmu.ne'
  have hρ0 : 0 ≤ lam / mu := div_nonneg h0 hmu.le
  have hρ1 : lam / mu < 1 := (div_lt_one hmu).mpr h1
  refine stationaryWeight_unique hρ0 hρ1 (fun n => ?_) hsum
  have h := cutFlow_eq_zero_of_summable hbal hsum.summable n
  unfold cutFlow at h
  field_simp
  linarith

/-- Mean number in system, `L = ∑ n·P(N = n)` (a `tsum`; junk `0` off the
summable range). The summand is written `(n : ℝ) * …` deliberately so the
reshaped form matches Mathlib's first-moment lemma syntactically. -/
noncomputable def meanQueue (ρ : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * stationaryWeight ρ n

/-- The disclosed junk corner, kernel-checked: off the summable range the
`tsum` in `meanQueue` collapses to `0`. At `ρ = 2` the summands
`n · (1-2) · 2ⁿ` do not tend to zero, so the family is not summable. -/
theorem meanQueue_two : meanQueue 2 = 0 := by
  unfold meanQueue
  refine tsum_eq_zero_of_not_summable fun hsum => ?_
  have hdiv : Filter.Tendsto (fun n : ℕ => (n : ℝ) * stationaryWeight 2 n)
      Filter.atTop Filter.atBot := by
    have heq : (fun n : ℕ => (n : ℝ) * stationaryWeight 2 n)
        = fun n : ℕ => -((n : ℝ) * 2 ^ n) := by
      funext n; unfold stationaryWeight; ring
    rw [heq]
    exact Filter.tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  exact not_tendsto_nhds_of_tendsto_atBot hdiv 0 hsum.tendsto_atTop_zero

/-- **The utilization law**: `L = ρ/(1-ρ)`. The mean queue is finite below
saturation and rides the hockey-stick this library's load-coupled kernels
descend from. -/
theorem meanQueue_eq {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    meanQueue ρ = ρ / (1 - ρ) := by
  have hnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hne : (1 : ℝ) - ρ ≠ 0 := by linarith
  unfold meanQueue
  calc ∑' n : ℕ, (n : ℝ) * stationaryWeight ρ n
      = ∑' n : ℕ, (1 - ρ) * ((n : ℝ) * ρ ^ n) :=
        tsum_congr fun n => by unfold stationaryWeight; ring
    _ = (1 - ρ) * ∑' n : ℕ, (n : ℝ) * ρ ^ n := tsum_mul_left
    _ = (1 - ρ) * (ρ / (1 - ρ) ^ 2) := by
        rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm]
    _ = ρ / (1 - ρ) := by
        field_simp

/-- Mean number waiting (excluding the in-service customer): the count over
the shifted distribution, `Lq = ∑ n·P(N = n+1)`. -/
noncomputable def meanQueueWaiting (ρ : ℝ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) * stationaryWeight ρ (n + 1)

/-- `Lq = ρ²/(1-ρ)`: the shifted first moment is `ρ` times the mean queue
(`stationaryWeight_succ`), so the law follows from `meanQueue_eq`. -/
theorem meanQueueWaiting_eq {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    meanQueueWaiting ρ = ρ ^ 2 / (1 - ρ) := by
  unfold meanQueueWaiting
  calc ∑' n : ℕ, (n : ℝ) * stationaryWeight ρ (n + 1)
      = ∑' n : ℕ, ρ * ((n : ℝ) * stationaryWeight ρ n) :=
        tsum_congr fun n => by rw [stationaryWeight_succ]; ring
    _ = ρ * meanQueue ρ := by unfold meanQueue; exact tsum_mul_left
    _ = ρ ^ 2 / (1 - ρ) := by rw [meanQueue_eq h0 h1]; ring

/-- `Lq + ρ = L`: the waiting count plus the in-service utilization is the
system count. -/
theorem meanQueueWaiting_add_util {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    meanQueueWaiting ρ + ρ = meanQueue ρ := by
  rw [meanQueueWaiting_eq h0 h1, meanQueue_eq h0 h1]
  have hne : (1 : ℝ) - ρ ≠ 0 := by linarith
  field_simp
  ring

/-- Pin of `Lq + ρ = L` at `ρ = 3/4` (`9/4 + 3/4 = 3`). The hypothesis
`ρ < 1` is load-bearing here, unlike in `meanQueue_eq`: at `ρ = 1` the
identity is genuinely false (`0 + 1 ≠ 0`), while `meanQueue_eq` is junk-true
there (both sides collapse to `0` for unrelated reasons). -/
theorem meanQueueWaiting_add_util_pin :
    meanQueueWaiting (3 / 4) + 3 / 4 = meanQueue (3 / 4) :=
  meanQueueWaiting_add_util (by norm_num) (by norm_num)

/-- The law is strictly increasing in utilization: more load, longer queue,
with no flat stretches to hide in. -/
theorem meanQueue_strictMonoOn :
    StrictMonoOn meanQueue (Set.Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [meanQueue_eq hx.1 hx.2, meanQueue_eq hy.1 hy.2]
  have hx1 : (0 : ℝ) < 1 - x := by linarith [hx.2]
  have hy1 : (0 : ℝ) < 1 - y := by linarith [hy.2]
  rw [div_lt_div_iff₀ hx1 hy1]
  linarith

open Filter Topology in
/-- **The knee**: the mean queue diverges as utilization approaches one from
below — the `1/(1-ρ)` blowup behind every congestion cliff. -/
theorem tendsto_meanQueue_atTop :
    Tendsto meanQueue (𝓝[<] (1 : ℝ)) atTop := by
  have hden : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝[<] (1 : ℝ))
      (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun ρ : ℝ => 1 - ρ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact sub_pos.mpr (Set.mem_Iio.mp hρ)
  have hmul := hden.inv_tendsto_nhdsGT_zero.atTop_mul_pos zero_lt_one
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hclosed : Tendsto (fun ρ : ℝ => ρ / (1 - ρ)) (𝓝[<] (1 : ℝ)) atTop := by
    refine hmul.congr fun ρ => ?_
    simp [div_eq_inv_mul]
  refine hclosed.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ρ hρ
  exact (meanQueue_eq hρ.1.le hρ.2).symm

/-- Mean time in system, with **Little's law taken as the definition**:
`W = L/λ`. The identity `L = λW` is the standard bridge from queue length
to delay; this library takes it as the interface (the same stance
`Overload/Verification/Suite.lean` takes for PASTA) rather than deriving it.
Total; the
closed form is `meanWait_eq` under `0 < λ < μ`. -/
noncomputable def meanWait (lam mu : ℝ) : ℝ := meanQueue (lam / mu) / lam

/-- **The delay law**: `W = 1/(μ-λ)` for a stable queue. Delay diverges
with shrinking headroom — the quantitative content of "it got slow before
it fell over". -/
theorem meanWait_eq {lam mu : ℝ} (h0 : 0 < lam) (h1 : lam < mu) :
    meanWait lam mu = (mu - lam)⁻¹ := by
  have hmu : 0 < mu := h0.trans h1
  have hρ0 : 0 ≤ lam / mu := div_nonneg h0.le hmu.le
  have hρ1 : lam / mu < 1 := (div_lt_one hmu).mpr h1
  unfold meanWait
  rw [meanQueue_eq hρ0 hρ1]
  have hne : mu - lam ≠ 0 := by linarith
  have hmune : mu ≠ 0 := hmu.ne'
  have hlamne : lam ≠ 0 := h0.ne'
  field_simp

/-- The two-sided boundary of the delay law, pinned. At saturation
(`λ = μ = 1`) the identity is **junk-true**: both sides collapse to `0` for
unrelated reasons (the weights vanish on the left, `0⁻¹ = 0` on the right).
Above saturation (`λ = 2, μ = 1`) it is genuinely false, so `λ < μ` is
load-bearing there and only there. -/
theorem meanWait_saturation_junk : meanWait 1 1 = ((1 : ℝ) - 1)⁻¹ := by
  unfold meanWait meanQueue
  simp [stationaryWeight]

/-- The refutation half of the two-sided boundary: at `λ = 2, μ = 1` the
delay-law identity is genuinely false, so `λ < μ` in `meanWait_eq` is
load-bearing there. A counterexample, not a general theorem. -/
theorem meanWait_false_above_saturation : meanWait 2 1 ≠ ((1 : ℝ) - 2)⁻¹ := by
  unfold meanWait
  rw [show (2 : ℝ) / 1 = 2 by norm_num, meanQueue_two]
  norm_num

/-- **The Little bridge, as a statement rather than as prose**: `L = λ·W`.
Given this file's definitions the identity is **definitional** — `meanWait`
*is* `L/λ`, so the only content is cancelling `λ`, and `lam ≠ 0` is what the
cancellation needs. Nothing ergodic is established here.
`Overload/Queueing/Little.lean` proves the deterministic sample-path law;
identifying its time averages with
these stationary quantities remains the documented open step. -/
theorem meanQueue_eq_lam_mul_meanWait {lam mu : ℝ} (hlam : lam ≠ 0) :
    meanQueue (lam / mu) = lam * meanWait lam mu := by
  unfold meanWait
  field_simp

/-- **The delay law with the ergodic identification hoisted into a
hypothesis.** For an externally supplied mean sojourn `W`, at `0 < λ < μ`
and assuming Little's identity `L = λ·W` — the step this file does not
prove — the utilization law yields `W = 1/(μ-λ)`. Carrying the assumption as a
hypothesis rather than as a definition is what puts the modeling gap in the
statement instead of only in the prose. -/
theorem meanWait_eq_of_little {lam mu W : ℝ} (h0 : 0 < lam) (h1 : lam < mu)
    (hlittle : meanQueue (lam / mu) = lam * W) : W = (mu - lam)⁻¹ := by
  have h := (meanQueue_eq_lam_mul_meanWait (mu := mu) h0.ne').symm.trans hlittle
  rw [← mul_left_cancel₀ h0.ne' h, meanWait_eq h0 h1]

/-- Numeric regression: half utilization holds one customer. -/
theorem meanQueue_half : meanQueue (1 / 2) = 1 := by
  rw [meanQueue_eq (by norm_num) (by norm_num)]
  norm_num

/-- Numeric regression on the documented bridge: at `λ = 1`, `μ = 2` the
utilization law holds one customer, and that is Little's identity at mean
sojourn `1` (`meanQueue (1/2) = 1·1`), so the bridge returns the delay
law's `1/(μ−λ) = 1`. The equation is immediate at these numbers; the pin
carries the satisfied Little hypothesis alongside it. -/
theorem meanWait_eq_of_little_pin :
    meanQueue (1 / 2) = 1 * 1 ∧ (1 : ℝ) = (2 - 1)⁻¹ :=
  ⟨by rw [meanQueue_half]; norm_num,
    meanWait_eq_of_little (by norm_num) (by norm_num)
      (by rw [meanQueue_half]; norm_num)⟩

/-- Numeric regression: `3/4` utilization holds three customers. -/
theorem meanQueue_three_quarters : meanQueue (3 / 4) = 3 := by
  rw [meanQueue_eq (by norm_num) (by norm_num)]
  norm_num

/-- Numeric regression: 1 req/s against capacity 2 waits one time unit. -/
theorem meanWait_one_two : meanWait 1 2 = 1 := by
  rw [meanWait_eq (by norm_num) (by norm_num)]
  norm_num

/-!
## The queueing-derived kernel

The law above is what makes failure load-coupled: as demand climbs toward
capacity, delay blows up, and any fixed timeout `τ` is eventually crossed.
`mm1Kernel` packages that as a failure kernel — the M/M/1 sojourn tail
`P(S > τ) = e^{-(C-Λ)τ}` below capacity, saturated at and above it. The
sojourn *distribution* is not derived here (that needs the stochastic
process); the tail form is a **modeling definition**, and what is proved is
everything downstream of it: kernel structure, monotone load coupling, and
the bistability of the resulting closed loop on the real kernel rather than
the step cartoon. The designated route for eventually *deriving* it is
Mathlib's Markov-kernel line (`Mathlib.Probability.Kernel.Invariance` and
descendants): build the M/M/1 process, derive the stationary sojourn
distribution, and discharge this definition into a theorem. Until that
theory exists (in Mathlib or anywhere), the honest boundary is drawn here.
-/

open Classical in
/-- The M/M/1 sojourn-tail kernel: an attempt times out with probability
`e^{-(C-Λ)τ}` below capacity (the exponential sojourn tail at headroom
`C - Λ`), and surely at or above capacity. A modeling definition — see the
section docstring. -/
noncomputable def mm1Kernel (C τ : ℝ) : ℝ → ℝ :=
  fun Λ => if Λ < C then Real.exp (-((C - Λ) * τ)) else 1

/-- Below capacity the kernel is the exponential sojourn tail. -/
theorem mm1Kernel_of_lt {C τ Λ : ℝ} (h : Λ < C) :
    mm1Kernel C τ Λ = Real.exp (-((C - Λ) * τ)) :=
  if_pos h

/-- At and above capacity the kernel saturates: attempts surely time out. -/
theorem mm1Kernel_of_ge {C τ Λ : ℝ} (h : C ≤ Λ) : mm1Kernel C τ Λ = 1 :=
  if_neg (not_lt.mpr h)

/-- The `τ = 0` degeneracy, disclosed: with a zero timeout the
"queueing-derived" kernel is the constant-1 (always-fail) kernel at every
load — `mm1Loop` at `τ = 0` is load-blind and therefore monostable
(`mm1FlatLoop_not_bistable`). `mm1Kernel_lt_one`'s `0 < τ` is what keeps the
kernel genuinely load-coupled. -/
theorem mm1Kernel_zero_tau (C Λ : ℝ) : mm1Kernel C 0 Λ = 1 := by
  unfold mm1Kernel
  split_ifs <;> simp

/-- For `0 ≤ τ` the kernel lands in `[0, 1]`. Supplies `g_mem` for
`mm1Loop`. -/
theorem mm1Kernel_mem {C τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ x, 0 ≤ x → mm1Kernel C τ x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x _
  unfold mm1Kernel
  split_ifs with hx
  · refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [Real.exp_le_one_iff]
    have h : 0 ≤ (C - x) * τ := mul_nonneg (by linarith) hτ
    linarith
  · exact ⟨by norm_num, le_rfl⟩

/-- For `0 ≤ τ` the kernel is monotone on `[0, ∞)`: shrinking headroom
raises the exponential sojourn tail. Supplies `g_mono` for `mm1Loop`. -/
theorem mm1Kernel_monoOn {C τ : ℝ} (hτ : 0 ≤ τ) :
    MonotoneOn (mm1Kernel C τ) (Set.Ici (0 : ℝ)) := by
  intro x _hx y _hy hxy
  unfold mm1Kernel
  split_ifs with hxC hyC hyC
  · rw [Real.exp_le_exp]
    have h : (C - y) * τ ≤ (C - x) * τ :=
      mul_le_mul_of_nonneg_right (by linarith) hτ
    linarith
  · rw [Real.exp_le_one_iff]
    have h : 0 ≤ (C - x) * τ := mul_nonneg (by linarith) hτ
    linarith
  · exact absurd (lt_of_le_of_lt hxy hyC) hxC
  · exact le_rfl

/-- Below capacity, at positive timeout, the exponential kernel is
genuinely below one — the honest contrast with the saturated step
cartoon, which jumps straight to certain failure. (`0 < τ` is
load-bearing: at `τ = 0` the kernel equals one.) -/
theorem mm1Kernel_lt_one {C τ Λ : ℝ} (hΛ : Λ < C) (hτ : 0 < τ) :
    mm1Kernel C τ Λ < 1 := by
  rw [mm1Kernel_of_lt hΛ, Real.exp_lt_one_iff]
  have h : 0 < (C - Λ) * τ := mul_pos (by linarith) hτ
  linarith

/-- Pin of `mm1Kernel_lt_one` at the band loop's numbers. Both strict
hypotheses are sharp: at `τ = 0` the kernel is `1` (`mm1Kernel_zero_tau`),
and at `Λ = C` it is `1` (`mm1Kernel_of_ge`). -/
theorem mm1Kernel_lt_one_pin : mm1Kernel 100 1 31 < 1 :=
  mm1Kernel_lt_one (by norm_num) one_pos

/-- `e^{-x} ≤ 1/(1+x)` for `x ≥ 0`: the workhorse bound that closes kernel
certificates by rational arithmetic. The content is Mathlib's
`Real.add_one_le_exp`; this is that bound inverted. -/
theorem exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (1 + x)⁻¹ := by
  rw [Real.exp_neg]
  have h1 : 1 + x ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  gcongr

/-- The M/M/1 loop: truncated-geometric retries (cap `m`) against the
exponential sojourn-tail kernel — a `ClosedLoop` whose load coupling comes
from the utilization law rather than a cartoon. -/
noncomputable def mm1Loop (lam C τ : ℝ) (m : ℕ) (hlam : 0 ≤ lam)
    (hτ : 0 ≤ τ) (hm : 1 ≤ m) : ClosedLoop :=
  kernelLoop lam (mm1Kernel C τ) m hlam hm (mm1Kernel_mem hτ)
    (mm1Kernel_monoOn hτ)

/-- The band instance of this section, bound once: offered load 30 against
capacity 100, unit timeout, 4-attempt cap. `mm1Loop_bistable`,
`mm1Loop_congestedEq`, and `mm1Loop_two_fixedPts` below all read on it, off
the two point evaluations `mm1BandLoop_healthy` and `mm1BandLoop_inflow`. -/
noncomputable abbrev mm1BandLoop : ClosedLoop :=
  mm1Loop 30 100 1 4 (by norm_num) (by norm_num) (by norm_num)

/-- The healthy leg of the M/M/1 band: at demand 31 inflow stays within
the level, `F(31) ≤ 31`. The margin lives inside the proof: the timeout
probability is bounded by `e^{-69} ≤ 1/70`, so amplification is at most
`70/69` and `30·70/69 < 31` closes the goal. -/
theorem mm1BandLoop_healthy : mm1BandLoop.F 31 ≤ 31 := by
  change (30 : ℝ) * expAttempts (mm1Kernel 100 1 31) 4 ≤ 31
  have hp : mm1Kernel 100 1 31 ≤ (1 / 70 : ℝ) := by
    rw [mm1Kernel_of_lt (by norm_num)]
    have heq : -((100 - 31 : ℝ) * 1) = -(69 : ℝ) := by norm_num
    rw [heq]
    have h := exp_neg_le_inv_one_add (x := (69 : ℝ)) (by norm_num)
    linarith
  have hp0 : 0 ≤ mm1Kernel 100 1 31 :=
    (mm1Kernel_mem (by norm_num) 31 (by norm_num)).1
  have hp1 : mm1Kernel 100 1 31 < 1 := lt_of_le_of_lt hp (by norm_num)
  have hgeo := expAttempts_le_geom_bound hp0 hp1 4
  have hden : (69 / 70 : ℝ) ≤ 1 - mm1Kernel 100 1 31 := by linarith
  have hinv : 1 / (1 - mm1Kernel 100 1 31) ≤ 1 / (69 / 70 : ℝ) := by
    gcongr
  linarith

/-- The congested leg of the M/M/1 band: at demand 100 the kernel saturates,
so `F(100) = 30·4 = 120 ≥ 100` — inflow at capacity already sustains it. -/
theorem mm1BandLoop_inflow : (100 : ℝ) ≤ mm1BandLoop.F 100 := by
  change (100 : ℝ) ≤ 30 * expAttempts (mm1Kernel 100 1 100) 4
  rw [mm1Kernel_of_ge (by norm_num), expAttempts_def, one_geom_sum]
  norm_num

/-- **Bistability on the queueing-derived kernel.** Offered load 30 against
capacity 100, unit timeout, 4-attempt cap: the healthy side holds at 31
because the timeout probability there is at most `e^{-69} ≤ 1/70`, so
amplification is at most `70/69` and `F(31) ≤ 30·70/69 < 31`
(`mm1BandLoop_healthy`); the congested side holds at 100, where the kernel
saturates and `F(100) = 120 ≥ 100` (`mm1BandLoop_inflow`). The band is real
on the real kernel, not only on the step cartoon. -/
theorem mm1Loop_bistable :
    BistableOn (mm1Loop 30 100 1 4 (by norm_num) (by norm_num)
      (by norm_num)).F 0 120 := by
  refine mm1BandLoop.bistableOn_of_two_points (by norm_num) mm1BandLoop_healthy
    mm1BandLoop_inflow (by norm_num) ?_
  change (30 : ℝ) * ((4 : ℕ) : ℝ) ≤ 120
  norm_num

/-- **The queueing-derived loop has a genuine congested equilibrium**: a
fixed point at or above capacity 100, from the saturated leg via the inflow
certificate. `mm1Loop_bistable` alone records only an order gap. -/
theorem mm1Loop_congestedEq : mm1BandLoop.CongestedEq 100 :=
  mm1BandLoop.congestedEq_of_inflow (by norm_num) mm1BandLoop_inflow

/-- **The M/M/1 band's equilibria are genuine.** The two point evaluations
behind `mm1Loop_bistable` upgrade to two distinct fixed points of the
queueing-derived loop — a healthy one at or below 31 and a congested one at
or above 100 — so bistability on the real kernel is a statement about
equilibria, not only about the `BistableOn` order gap. -/
theorem mm1Loop_two_fixedPts :
    ∃ z₁ z₂, Function.IsFixedPt mm1BandLoop.F z₁ ∧
      Function.IsFixedPt mm1BandLoop.F z₂ ∧ z₁ ≤ 31 ∧ 100 ≤ z₂ ∧ z₁ < z₂ :=
  mm1BandLoop.two_fixedPts_of_two_points (by norm_num) mm1BandLoop_healthy
    mm1BandLoop_inflow (by norm_num)

open Filter in
/-- **The cartoon justified**: below capacity the exponential kernel
vanishes pointwise as `τ → ∞` — exactly `stepKernel`'s value there. This
is the `Λ < C` leg of the sharp-timeout limit; the saturated leg is
`mm1Kernel_of_ge`, where the two kernels agree at `1` outright. -/
theorem mm1Kernel_tendsto_zero {C Λ : ℝ} (hΛ : Λ < C) :
    Tendsto (fun τ => mm1Kernel C τ Λ) atTop (nhds 0) := by
  have hpos : 0 < C - Λ := by linarith
  have hlin : Tendsto (fun τ : ℝ => (C - Λ) * τ) atTop atTop :=
    Tendsto.const_mul_atTop hpos tendsto_id
  have hneg : Tendsto (fun τ : ℝ => -((C - Λ) * τ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hlin
  have hexp := Real.tendsto_exp_atBot.comp hneg
  exact hexp.congr fun τ => (mm1Kernel_of_lt hΛ).symm

open Filter in
/-- Pin of the sharp-timeout limit at the band loop's numbers. The strict
`Λ < C` is sharp: at `Λ = C` the kernel is `1` for every `τ`
(`mm1Kernel_of_ge`), so the limit there is `1`, not `0`. -/
theorem mm1Kernel_tendsto_zero_pin :
    Tendsto (fun τ => mm1Kernel 100 τ 31) atTop (nhds 0) :=
  mm1Kernel_tendsto_zero (by norm_num)

/-- The band loop with its timeout dropped to zero: same load 30, capacity
100, cap 4 as `mm1BandLoop`, but `τ = 0` makes the kernel constant
(`mm1Kernel_zero_tau`), so the loop is load-blind. -/
noncomputable abbrev mm1FlatLoop : ClosedLoop :=
  mm1Loop 30 100 0 4 (by norm_num) le_rfl (by norm_num)

/-- **The timeout is what creates the band**: the very numbers that are
bistable at `τ = 1` (`mm1Loop_bistable`) are provably monostable at `τ = 0`,
by `not_bistableOn_of_const` over the constant kernel. -/
theorem mm1FlatLoop_not_bistable : ¬BistableOn mm1FlatLoop.F 0 120 := by
  have h : mm1FlatLoop.lam * mm1FlatLoop.Amax = 120 := by
    change (30 : ℝ) * ((4 : ℕ) : ℝ) = 120
    norm_num
  rw [← h]
  exact mm1FlatLoop.not_bistableOn_of_const fun x _ => mm1Kernel_zero_tau 100 x

end Overload
