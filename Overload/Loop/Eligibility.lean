module

public import Overload.Basic -- shake: keep
public import Overload.Loop.ClosedLoop
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
import Overload.Loop.Hysteresis

/-!
# Demand-side eligibility: the miscoded signal as an amplification mechanism

The translation map decides more than what a dashboard sees
(`Observability.lean` is the instrument side of that lesson): the emitted
label also decides which outcomes a *client's retry policy* treats as
retry-eligible. The demand-side translation into the loop framework:

* `ClosedLoop.congestedEq_mono_response` — congestion transfers up the
  response order: the response-side mirror of `congestedEq_mono_lam` and
  `congestedEq_mono_kernel`.
* `eligibleResponse_mono_mass` — failure mass moved into the eligible set
  raises the amplification response pointwise.
* `eligibleLoop_congestedEq_mono_mass` — chaining the two: the congested
  set of the eligibility-coded loop weakly enlarges as the mass grows.
* `miscoding_opens_amplification` — the corollary: with the eligible set
  empty the loop is `NoSustaining` (`h ≡ 1`); recoding any positive
  failure mass as retry-eligible under a real retry budget yields `1 < h`
  at kernel saturation. A label rewrite, with load, kernel, and budget
  untouched, manufactures the sustaining mechanism the `noSustaining`
  audit looks for.
-/

@[expose] public section

namespace Overload

/-- **Congestion transfers up the response order** — the response-side
mirror of `congestedEq_mono_lam` and `congestedEq_mono_kernel`: a congested
equilibrium under a pointwise-smaller response on `[0,1]` (same offered
load, kernel agreeing at nonnegative loads) is a postfixed point of the
reference loop, and Knaster–Tarski re-supplies a genuine equilibrium above
it. Contrapositive: safety covers every smaller-response sibling. -/
theorem ClosedLoop.congestedEq_mono_response (L : ClosedLoop)
    {M : BoundedLoop} (hlam : M.lam = L.lam)
    (hg : ∀ x, 0 ≤ x → M.g x = L.g x)
    (hle : ∀ p ∈ Set.Icc (0 : ℝ) 1, M.h p ≤ L.h p) {Θ : ℝ}
    (hcong : M.CongestedEq Θ) : L.CongestedEq Θ := by
  obtain ⟨Λ, hΛ0, hfix, hΘΛ⟩ := hcong
  have hpost : Λ ≤ L.F Λ := by
    calc Λ = M.lam * M.h (M.g Λ) := hfix.symm
      _ = L.lam * M.h (L.g Λ) := by rw [hlam, hg Λ hΛ0]
      _ ≤ L.lam * L.h (L.g Λ) :=
          mul_le_mul_of_nonneg_left (hle _ (L.g_mem Λ hΛ0)) L.lam_nonneg
      _ = L.F Λ := rfl
  exact (L.congestedEq_of_inflow hΛ0 hpost).mono hΘΛ

/-- **The congested set weakly enlarges with the attempt cap**: raising the
cap of a truncated-geometric loop never removes a congested equilibrium —
`expAttempts_mono_right` chained through `congestedEq_mono_response`. The
cap-side reading of the same monotonicity: the attempt cap is the operational
knob, and safety certified at a cap covers every smaller one. -/
theorem kernelLoop_congestedEq_mono_cap {lam : ℝ} {g : ℝ → ℝ} {m m' : ℕ}
    (hlam : 0 ≤ lam) (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))) (hmm' : m ≤ m') {Θ : ℝ}
    (hcong : (kernelLoop lam g m hlam hm hg_mem hg_mono).CongestedEq Θ) :
    (kernelLoop lam g m' hlam hm' hg_mem hg_mono).CongestedEq Θ :=
  (kernelLoop lam g m' hlam hm' hg_mem hg_mono).congestedEq_mono_response
    (M := (kernelLoop lam g m hlam hm hg_mem hg_mono).toBoundedLoop)
    rfl (fun _ _ => rfl)
    (fun _p hp => expAttempts_mono_right hp.1 hmm') hcong

/-- The eligibility-coded amplification response: retries are driven only
by the fraction `e` of failure mass whose emitted label codes it
retry-eligible — the truncated-geometric response at the eligible failure
level `e·p`. Total for every real `e` and `p` (a polynomial); the intended
domain is `e, p ∈ [0,1]`, and every result below carries its hypotheses. -/
noncomputable def eligibleResponse (e : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun p => expAttempts (e * p) m

/-- **Mass moved into the eligible set raises the response pointwise**: the
eligibility-coded response is monotone in the eligible mass. -/
theorem eligibleResponse_mono_mass {e e' : ℝ} (he : 0 ≤ e) (hee' : e ≤ e')
    (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    eligibleResponse e m p ≤ eligibleResponse e' m p :=
  expAttempts_mono_left (mul_nonneg he hp)
    (mul_le_mul_of_nonneg_right hee' hp) m

/-- The closed loop with the eligibility-coded response over an arbitrary
kernel: `kernelLoop` with the retry-eligible fraction `e` made explicit
(`e = 1` reads every failure as eligible; `e = 0` reads none). -/
noncomputable def eligibleLoop (lam : ℝ) (g : ℝ → ℝ) (m : ℕ) (e : ℝ)
    (hlam : 0 ≤ lam) (hm : 1 ≤ m)
    (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)))
    (he : e ∈ Set.Icc (0 : ℝ) 1) : ClosedLoop where
  lam := lam
  g := g
  h := eligibleResponse e m
  Amax := m
  lam_nonneg := hlam
  g_mem := hg_mem
  g_mono := hg_mono
  h_mono := fun _p hp _q _hq hpq => expAttempts_mono_left
    (mul_nonneg he.1 hp.1) (mul_le_mul_of_nonneg_left hpq he.1) m
  h_one_le := fun _p hp => one_le_expAttempts (mul_nonneg he.1 hp.1) hm
  h_le_Amax := fun _p hp => expAttempts_le_cap (mul_nonneg he.1 hp.1)
    (mul_le_one₀ he.2 hp.1 hp.2) m

variable {lam : ℝ} {g : ℝ → ℝ} {m : ℕ} {e e' : ℝ} {hlam : 0 ≤ lam}
  {hm : 1 ≤ m} {hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1}
  {hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))} {he : e ∈ Set.Icc (0 : ℝ) 1}
  {he' : e' ∈ Set.Icc (0 : ℝ) 1}

/-- **The congested set weakly enlarges with the eligible mass**: coding
more failure mass retry-eligible never removes a congested equilibrium —
`eligibleResponse_mono_mass` chained through `congestedEq_mono_response`.
Contrapositive: safety certified at the looser coding `e'` covers every
tighter coding `e ≤ e'`. -/
theorem eligibleLoop_congestedEq_mono_mass (hee' : e ≤ e') {Θ : ℝ}
    (hcong :
      (eligibleLoop lam g m e hlam hm hg_mem hg_mono he).CongestedEq Θ) :
    (eligibleLoop lam g m e' hlam hm hg_mem hg_mono he').CongestedEq Θ :=
  (eligibleLoop lam g m e' hlam hm hg_mem hg_mono
    he').congestedEq_mono_response
    (M := (eligibleLoop lam g m e hlam hm hg_mem hg_mono he).toBoundedLoop)
    rfl (fun _ _ => rfl)
    (fun _p hp => eligibleResponse_mono_mass he.1 hee' m hp.1) hcong

/-- **Empty eligible set ⟹ no sustaining mechanism**: with no failure mass
coded retry-eligible the response is identically `1` — retries are
configured (`m` attempts allowed) but never fire, so the audit
(`noSustaining_no_congestedEq`) certifies any `λ < C` safe outright. -/
theorem eligibleLoop_zero_noSustaining :
    (eligibleLoop lam g m 0 hlam hm hg_mem hg_mono
      ⟨le_rfl, zero_le_one⟩).NoSustaining := by
  intro p _hp
  change expAttempts (0 * p) m = 1
  rw [zero_mul, expAttempts_at_zero hm]

/-- **The miscoding corollary.** Same offered load, kernel, and retry
budget; only the label coding differs. With the eligible set empty the
loop is `NoSustaining` (`h ≡ 1`); recode any positive failure mass `e` as
retry-eligible under a real retry budget (`2 ≤ m`) and the response
strictly exceeds `1` at kernel saturation. -/
theorem miscoding_opens_amplification (he0 : 0 < e) (hm2 : 2 ≤ m) :
    (eligibleLoop lam g m 0 hlam hm hg_mem hg_mono
        ⟨le_rfl, zero_le_one⟩).NoSustaining ∧
      1 < (eligibleLoop lam g m e hlam hm hg_mem hg_mono he).h 1 := by
  refine ⟨eligibleLoop_zero_noSustaining, ?_⟩
  change 1 < expAttempts (e * 1) m
  have h1 := one_add_le_expAttempts (mul_nonneg he.1 zero_le_one) hm2
  linarith

/-- The demonstration family: offered load `2`, step kernel at capacity
`3`, retry budget `5`, eligible mass `e`. -/
noncomputable abbrev demoEligibleLoop (e : ℝ) (he : e ∈ Set.Icc (0 : ℝ) 1) :
    ClosedLoop :=
  eligibleLoop 2 (stepKernel 3) 5 e (by norm_num) (by norm_num)
    (stepKernel_mem 3) (stepKernel_monoOn 3) he

/-- Numeric regression, honest leg: nothing eligible, `λ = 2 < 3 = C`, safe
outright. -/
theorem demoEligibleLoop_zero_no_congestedEq :
    ¬(demoEligibleLoop 0 ⟨le_rfl, zero_le_one⟩).CongestedEq 3 :=
  (demoEligibleLoop 0 ⟨le_rfl, zero_le_one⟩).noSustaining_no_congestedEq
    eligibleLoop_zero_noSustaining (show (2 : ℝ) < 3 by norm_num)

/-- Numeric regression, miscoded leg and chain: half the mass eligible
already congests (inflow at `Θ = 3` is `2·expAttempts (1/2) 5 = 31/8 ≥ 3`),
and it transfers up to full miscoding `e = 1`. -/
theorem demoEligibleLoop_one_congestedEq :
    (demoEligibleLoop 1 ⟨zero_le_one, le_rfl⟩).CongestedEq 3 := by
  refine eligibleLoop_congestedEq_mono_mass (e := 1 / 2)
    (he := by constructor <;> norm_num) (by norm_num) ?_
  refine ClosedLoop.congestedEq_of_inflow _ (by norm_num) ?_
  change (3 : ℝ) ≤ 2 * expAttempts (1 / 2 * stepKernel 3 3) 5
  rw [stepKernel_of_ge le_rfl, mul_one]
  norm_num [expAttempts, Finset.sum_range_succ]

/-- Numeric regression on the cap-side reading: a truncated-geometric loop
whose offered load `2` already meets the threshold is congested at cap `1`,
and raising the cap to `3` leaves it congested. Safety certified at a cap
covers the smaller caps, not the larger ones. -/
theorem kernelLoop_congestedEq_mono_cap_pin :
    (kernelLoop 2 (stepKernel 2) 3 (by norm_num) (by norm_num)
      (stepKernel_mem 2) (stepKernel_monoOn 2)).CongestedEq 2 :=
  kernelLoop_congestedEq_mono_cap (m := 1) (by norm_num) (by norm_num)
    (by norm_num) (stepKernel_mem 2) (stepKernel_monoOn 2) (by norm_num)
    ((kernelLoop 2 (stepKernel 2) 1 (by norm_num) (by norm_num)
      (stepKernel_mem 2) (stepKernel_monoOn 2)).congestedEq_of_over
        (show (2 : ℝ) ≤ 2 from le_rfl))

/-- Numeric regression, the miscoding corollary at the demonstration
numbers: no sustaining at `e = 0`, and at `e = 1` amplification above one
at kernel saturation (`p = 1`). -/
theorem demoEligibleLoop_miscoding_opens_amplification :
    (demoEligibleLoop 0 ⟨le_rfl, zero_le_one⟩).NoSustaining ∧
    1 < (demoEligibleLoop 1 ⟨zero_le_one, le_rfl⟩).h 1 :=
  miscoding_opens_amplification (by norm_num) (by norm_num)

end Overload
