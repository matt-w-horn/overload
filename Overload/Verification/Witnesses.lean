module

public import Overload.Basic -- shake: keep
public import Overload.Verification.Suite
public import Overload.Stack.Coupling
public import Overload.Queueing.Little
public import Overload.Capacity.Plateau
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
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Witnesses: the hypothesis bundles are satisfiable

The kernel checks proofs, not relevance: a theorem whose hypothesis bundle
cannot be satisfied is vacuously true and worthless. Statement-first
repositories guard against this with explicit test instances (the
formal-conjectures `category test` discipline); this file is the same guard
for the hypothesis-heavy structures here that the examples do not already
instantiate.

* `witnessFacts` / `witnessSuite` — a one-station system whose books satisfy
  the entire `VerificationSuite`, so the suite's constraints are mutually
  consistent and `goodput_bound` / `dual_total` are not vacuous.
* `certificateWitness` — a concrete two-site coupling matrix with a positive
  contracted weight vector: `Certificate` is inhabited directly, not only
  characterized by `two_site_certificate_iff`.
* `noRetryLoop` — a closed loop whose amplification response is identically
  one, realizing the `NoSustaining` hypothesis of the sustaining-mechanisms
  audit.
* `unitPath` — the unit-spaced trace (`aₙ = n`, `dₙ = n + 1`) discharging the
  whole sample-path bundle of `Little.lean` at `τ = Wbar = Gbar = 1`: H1, H2, and
  H3 hold simultaneously, so `SamplePath.little` and `SamplePath.brumelle`
  are not vacuous.

`stepLoop`, `dlqLoop`, `borgAcct`, and the layer stacks in
`Overload/Examples/` already witness `ClosedLoop`, `Accounting`,
`BistableOn`, `CongestedEq`, and `Layer`.
-/

@[expose] public section

namespace Overload

/-- A one-station, one-request window with coherent books, in the units the
`SystemFacts` field docstrings state. The story: one request arrives in a
unit window (`offered = 1`), makes two attempts at the station (one failure,
one success: `attempts = 2`, so `sent = received = 2` window-total attempts
and the attempt rate is `2` with mean sojourn `1/2`, giving time-averaged
occupancy `1`), completes usefully (`goodput = 1`); each attempt costs one
work unit against capacity 10, so the window splits `1` useful + `1` wasted
(the failed attempt) + `8` idle; the single failure has ground-truth origin
`0` emitted as wire code `0`, so both marginals are `(1, 0)`. -/
noncomputable def witnessFacts : SystemFacts (Fin 1) (Fin 1) (Fin 2) (Fin 2) where
  stations := Finset.univ
  requests := Finset.univ
  sent := fun _ => 2
  received := fun _ => 2
  inflight := fun _ => 1
  rate := fun _ => 2
  sojourn := fun _ => 1 / 2
  acct :=
    { capacity := 10, time := 1, useful := 1, wasted := 1, idle := 8
      capacity_pos := by norm_num, time_pos := by norm_num
      useful_nonneg := by norm_num, wasted_nonneg := by norm_num
      idle_nonneg := by norm_num, conserve := by norm_num }
  goodput := 1
  offered := 1
  sbar := 1
  attempts := fun _ _ => 2
  cap := fun _ => 3
  spent := fun _ => 1
  deadline := 5
  issued := 4
  consumed := 2
  outstanding := 1
  expired := 1
  joint := fun o w => if o = 0 ∧ w = 0 then 1 else 0
  originCount := fun o => if o = 0 then 1 else 0
  wireCount := fun w => if w = 0 then 1 else 0

/-- The suite holds of the witness: every numeric field closes by
arithmetic on the witness numerals, and the PASTA parameter is
instantiated at `True` — the sampling-unbiasedness proposition is
supplied trivially, not certified. This is the satisfiability certificate
for the numeric side of the `Prop`-bundle. -/
theorem witnessSuite : VerificationSuite True witnessFacts where
  flow_balance := fun _ _ => rfl
  useful_work := by norm_num [witnessFacts]
  goodput_le_offered := by norm_num [witnessFacts]
  little := fun _st _ => by norm_num [witnessFacts]
  deadline_budget := fun _r _ => by norm_num [witnessFacts]
  stopping := fun _ _ _ _ => by norm_num [witnessFacts]
  tokens := by norm_num [witnessFacts]
  origin_marginal := Fin.forall_fin_two.mpr
    ⟨by simp [witnessFacts], by simp [witnessFacts]⟩
  wire_marginal := Fin.forall_fin_two.mpr
    ⟨by simp [witnessFacts], by simp [witnessFacts]⟩
  pasta := trivial

/-- Numeric regression on the witness: goodput `1 ≤ min 1 (10/1)`. -/
theorem witnessFacts_goodput_bound :
    witnessFacts.goodput ≤ min witnessFacts.offered
    (witnessFacts.acct.capacity / witnessFacts.sbar) :=
  witnessSuite.goodput_bound (by norm_num [witnessFacts])

/-- Numeric regression on the witness: the two failure marginals agree, and
their common total is `1` rather than zero — the single failure is counted
once on each side of the translation. -/
theorem witnessFacts_dual_total :
    ∑ o, witnessFacts.originCount o = ∑ w, witnessFacts.wireCount w ∧
      ∑ o, witnessFacts.originCount o = 1 :=
  ⟨witnessSuite.dual_total, by simp [witnessFacts]⟩

/-- A concrete stable coupling: local gains `1/2`, cross-couplings `1/4`,
contracted by the uniform weight vector (`3/4 < 1` per row). -/
theorem certificateWitness : Certificate !![1/2, 1/4; 1/4, 1/2] :=
  certificate_of_two (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_pos one_pos (by norm_num) (by norm_num)

/-- Numeric regression on the accounting bridge: one class offering `1` at cap
`2` under capacity `4` plateaus at goodput `1`, so the witness accounting's
waste fraction of `1/10` puts measured goodput below the plateau. The theorem
then returns strictly positive wasted work — the inequality itself is
immediate at these numbers; what the pin exercises is the route through
`plateau`. -/
theorem witnessFacts_cliff_implies_wasted : 0 < witnessFacts.acct.wasted :=
  cliff_implies_wasted (s := (Finset.univ : Finset (Fin 1)))
    (lam := fun _ => 1) (cap := fun _ => 2) (C := 4) (p := 0) (w := 1 / 10)
    witnessFacts.acct (by norm_num)
    (show (1 : ℝ) = 1 / 10 * (10 * 1) by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (Or.inl ⟨rfl, by norm_num [attemptRate, expAttempts]⟩)
    (by norm_num [goodput])

/-- Numeric regression on the rate extraction: the concrete stable coupling
hands `certificate_decay` a weight vector and a rate strictly below one, which
a bare certificate does not. -/
theorem certificateWitness_rate :
    ∃ w : Fin 2 → ℝ, ∃ ρ : ℝ, (∀ i, 0 < w i) ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ i, (!![1/2, 1/4; 1/4, 1/2] : Matrix (Fin 2) (Fin 2) ℝ).mulVec w i
        ≤ ρ * w i :=
  certificate_rate certificateWitness

/-- A loop that never retries: the amplification response is identically one,
whatever the kernel reports. -/
noncomputable def noRetryLoop (lam : ℝ) (hlam : 0 ≤ lam) : ClosedLoop where
  lam := lam
  g := fun _ => 0
  h := fun _ => 1
  Amax := 1
  lam_nonneg := hlam
  g_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  g_mono := monotoneOn_const
  h_mono := monotoneOn_const
  h_one_le := fun _ _ => le_rfl
  h_le_Amax := fun _ _ => le_rfl

/-- The sustaining-mechanisms audit's hypothesis is realizable: the no-retry
loop satisfies `NoSustaining` on the nose. -/
theorem noRetryLoop_noSustaining (lam : ℝ) (hlam : 0 ≤ lam) :
    (noRetryLoop lam hlam).NoSustaining := fun _ _ => rfl

/-- Numeric regression on the sustaining-mechanisms audit: a no-retry loop
at load `1` below capacity `2` has no congested equilibrium. -/
theorem noRetryLoop_no_congestedEq :
    ¬(noRetryLoop 1 (by norm_num)).CongestedEq 2 :=
  (noRetryLoop 1 (by norm_num)).noSustaining_no_congestedEq
    (noRetryLoop_noSustaining 1 (by norm_num))
    (by change (1 : ℝ) < 2; norm_num)

/-- Numeric regression on the zero-budget reduction: the no-retry loop meets
the response ceiling `h ≤ 1` on the nose, so load `3` under threshold `5`
leaves no congested equilibrium. -/
theorem noRetryLoop_reduction_budget_zero :
    ¬(noRetryLoop 3 (by norm_num)).CongestedEq 5 :=
  reduction_budget_zero (noRetryLoop 3 (by norm_num)).toBoundedLoop
    (fun _ _ => le_rfl) (by change (3 : ℝ) < 5; norm_num)

/-- A `BoundedLoop` that is not a `ClosedLoop`: a backpressure client whose
response *falls* with the failure level (`h p = 5·(1−p)`), violating the
`ClosedLoop` floor `1 ≤ h` at saturation. It inhabits the boundedness core
strictly — the split's safety-only side is satisfiable on its own. -/
noncomputable def backpressureLoop : BoundedLoop where
  lam := 1
  g := stepKernel 1
  h := fun p => 5 * (1 - p)
  Amax := 5
  lam_nonneg := zero_le_one
  g_mem := stepKernel_mem 1
  h_le_Amax := fun p hp => by nlinarith [hp.1]

/-- The backpressure loop violates the `ClosedLoop` response floor at
saturation: `h 1 = 0 < 1`. -/
theorem backpressureLoop_not_one_le : ¬(1 : ℝ) ≤ backpressureLoop.h 1 := by
  change ¬(1 : ℝ) ≤ 5 * (1 - 1)
  norm_num

/-- The disclosed `CongestedEq` asymmetry, bounded side, kernel-checked: the
backpressure operator has **no** fixed point on `[0, ∞)` at all (`F = 5`
below the kernel step at `1`, `F = 0` at or above it), so `CongestedEq`
fails at *every* threshold — including `Θ ≤ 0`, where every `ClosedLoop`
satisfies it (`ClosedLoop.congestedEq_of_nonpos_threshold`). -/
theorem backpressureLoop_no_congestedEq (Θ : ℝ) :
    ¬backpressureLoop.CongestedEq Θ := by
  rintro ⟨Λ, -, hfix, -⟩
  rw [show backpressureLoop.F Λ = 1 * (5 * (1 - stepKernel 1 Λ)) from rfl]
    at hfix
  rcases lt_or_ge Λ 1 with h | h
  · rw [stepKernel_of_lt h] at hfix; linarith
  · rw [stepKernel_of_ge h] at hfix; linarith

/-- The disclosed `CongestedEq` degeneracy, closed-loop side, at a strictly
negative threshold: the stylized band loop satisfies `CongestedEq (-5)`
through its healthy fixed point `Λ = 3`. -/
theorem stepLoop_congestedEq_neg :
    (stepLoop 3 10 5 (by norm_num) (by norm_num)).CongestedEq (-5) :=
  ⟨3, by norm_num,
    stepLoop_F_of_lt (by norm_num) (by norm_num) (by norm_num), by norm_num⟩

/-- A `BoundedLoop` whose declared envelope is far looser than its response:
`h p = 1 + p` under `Amax = 100`. Every concrete loop elsewhere has
`Amax = sup h`, where the budget corollary coincides with the raw envelope
bound `F_le`; here the budget does real work. -/
noncomputable def looseBudgetLoop : BoundedLoop where
  lam := 1
  g := stepKernel 10
  h := fun p => 1 + p
  Amax := 100
  lam_nonneg := zero_le_one
  g_mem := stepKernel_mem 10
  h_le_Amax := fun p hp => by linarith [hp.2]

/-- `budget_no_congestedEq` exercised where the budget (`β = 1`, so
`λ(1+β) = 2 < 10`) is strictly tighter than the declared envelope
(`F_le` gives only `F ≤ 100`): no congested equilibrium at threshold 10. -/
theorem looseBudgetLoop_safe : ¬looseBudgetLoop.CongestedEq 10 :=
  looseBudgetLoop.budget_no_congestedEq (β := 1)
    (fun p hp => by change (1 : ℝ) + p ≤ 1 + 1; linarith [hp.2])
    (by change (1 : ℝ) * (1 + 1) < 10; norm_num)

/-!
## The sample-path bundle

`Little.lean`'s `little` and `brumelle` carry three hypotheses at once — an
arrival rate, a Cesàro sojourn mean, and a Cesàro value mean. The unit-spaced
trace satisfies all three, with every rate equal to one.
-/

/-- The unit-spaced trace: customer `n` arrives at `n` and departs at `n + 1`,
so every sojourn is exactly `1`. -/
def unitPath : SamplePath where
  a := fun n => (n : ℝ)
  d := fun n => (n : ℝ) + 1
  a_nonneg := fun n => Nat.cast_nonneg n
  a_le_d := fun _ => by linarith
  a_mono := fun _ _ h => Nat.cast_le.mpr h

/-- On the unit-spaced trace the cumulative sojourn is the customer count. -/
theorem unitPath_sojournSum (n : ℕ) : unitPath.sojournSum n = n := by
  change ∑ k ∈ Finset.range n, (((k : ℝ) + 1) - (k : ℝ)) = n
  rw [Finset.sum_congr rfl (fun k _ => by ring : ∀ k ∈ Finset.range n,
    ((k : ℝ) + 1) - (k : ℝ) = 1)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Numeric regression on the sojourn interface: the unit-spaced trace holds
customer `5` for exactly `1`, which the nonnegativity pin bounds below. -/
theorem unitPath_W_nonneg : 0 ≤ unitPath.W 5 ∧ unitPath.W 5 = 1 :=
  ⟨unitPath.W_nonneg 5, by change ((5 : ℝ) + 1) - (5 : ℝ) = 1; norm_num⟩

/-- **H1 on the unit-spaced trace**: arrivals have rate `1` (`τ = 1`). The
shape all three hypotheses take here is `n / n → 1`, which is Mathlib's
`tendsto_natCast_div_add_atTop` at `x = 0`. -/
theorem unitPath_H1 :
    Filter.Tendsto (fun n : ℕ => unitPath.a n / n) Filter.atTop (nhds 1) := by
  change Filter.Tendsto (fun n : ℕ => (n : ℝ) / n) Filter.atTop (nhds 1)
  simpa using tendsto_natCast_div_add_atTop (0 : ℝ)

/-- **H2 on the unit-spaced trace**: the Cesàro sojourn mean is `Wbar = 1`. -/
theorem unitPath_H2 :
    Filter.Tendsto (fun n : ℕ => unitPath.sojournSum n / n) Filter.atTop
      (nhds 1) := by
  simpa only [unitPath_sojournSum, add_zero] using
    tendsto_natCast_div_add_atTop (0 : ℝ)

/-- **H3 on the unit-spaced trace**, at unit weight: the Cesàro value mean is
`Gbar = 1`. -/
theorem unitPath_H3 :
    Filter.Tendsto (fun n : ℕ => unitPath.valueSum (fun _ => 1) n / n)
      Filter.atTop (nhds 1) := by
  simpa only [SamplePath.valueSum_one, unitPath_sojournSum, add_zero] using
    tendsto_natCast_div_add_atTop (0 : ℝ)

/-- The bundle discharged: `SamplePath.little` applies to the unit-spaced
trace and returns the time-average number in system `λ·Wbar = 1`. H1 and H2 are
therefore jointly satisfiable. -/
theorem unitPath_little :
    Filter.Tendsto (fun t => unitPath.area t / t) Filter.atTop (nhds 1) := by
  simpa using unitPath.little (one_pos : (0 : ℝ) < 1) unitPath_H1 unitPath_H2

/-- The weighted bundle discharged: `SamplePath.brumelle` applies at unit
weight and returns the time-average value in system `λ·Gbar = 1`. H1, H2, and H3
are jointly satisfiable. -/
theorem unitPath_brumelle :
    Filter.Tendsto (fun t => unitPath.valueArea (fun _ => 1) t / t)
      Filter.atTop (nhds 1) := by
  simpa using unitPath.brumelle (one_pos : (0 : ℝ) < 1)
    (fun _ => zero_le_one) unitPath_H1 unitPath_H2 unitPath_H3

end Overload
