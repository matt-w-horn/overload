module

public import Overload.Basic -- shake: keep
public import Overload.Loop.ClosedLoop
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
# Signature incompleteness: the exported number does not decide the phase

The fan-in contract (`Star.lean`) exports one scalar per server; this file
studies its single-loop form — the signature `σ = λ·Amax`, offered load times the
declared response bound (unit fan-out; cf. `Star.signature`, the weighted
`λᵢKᵢrᵢ`). `σ < Θ` certifies safety (`signature_lt_no_congestedEq`, the
clamp theorem at `K = Amax`), and this file proves the matching
impossibility: no certificate that factors through `σ` — equal-signature
loops, equal verdicts; equivalently any `Q ∘ signature`
(`factorsThroughSignature_iff`) — decides congestion at a threshold inside
the envelope, or the two-equilibria phase structure. The instrument is an
equal-signature pair of plain `stepLoop`s splitting one σ two ways: base
load `λ` amplifying to `A` behind capacity (the threshold split) versus
base load `λ·A` amplifying not at all (the flat split). Same signature,
same kernel, same capacity; the signature forgets the split.

* `BoundedLoop.signature` — the exported scalar `σ = λ·Amax`.
* `FactorsThroughSignature` / `factorsThroughSignature_iff` — the
  certificate class: fiber-constancy, characterized as factorization.
* `no_signature_cert_of_separating_pair` — the separation principle.
* `signature_not_decide_congestedEq` / `signature_not_decide_two_fixedPts`
  — the incompleteness, certificate-outcome and phase-structure forms.
* `band_pair_both_congestedEq` / `band_pair_phase_divergent` — in the band
  the pair *agrees* on congestion and still splits on phase structure, so
  the signature's blindness is not an artifact of the congestion verdict.
* `headroomLoop` / `flatLoop` — the concrete pair at `σ = 4`, threshold
  `3`: equal signature, one safe, one congested
  (`signature_gap_witnessed`).

Beside `Tightness`: there, safety under a fixed kernel certifies nothing
about sibling kernels; here, the exported scalar certifies nothing about
the phase of a fixed loop. Neither weakens the positive direction —
`σ < Θ` still certifies safety, and over the kernel-quantified family the
pointwise clamp is exact. The coarsest-summary question is bracketed from
both sides: the scalar `λ·Amax` does not decide congestion or the
two-equilibria phase (this file), while the dimensionless pair
`(ρ₀ = λ/C, A)` decides the phase regions exactly
(`phase_matches_of_rho_eq`). (`Scheme`'s `(p, cap)` scheme signature is a
different object; "signature" here is the fan-in contract scalar.)
-/

@[expose] public section

namespace Overload

namespace BoundedLoop

variable (L : BoundedLoop)

/-- The scalar signature of a loop: offered load times declared response
bound, `σ = λ·Amax` — the one number a clamp certificate exports
(cf. `Star.signature`, the fan-out-weighted per-server form `λᵢKᵢrᵢ`).
The definition reads nothing else: not the shape of `h` below its bound,
not the kernel, not the capacity. -/
noncomputable def signature : ℝ := L.lam * L.Amax

/-- The signature certifies safety in one direction: `σ < Θ` removes every
congested equilibrium (the clamp theorem at `K = Amax`). The incompleteness
theorems below show no reading of `σ` can be complete. -/
theorem signature_lt_no_congestedEq {Θ : ℝ} (hσ : L.signature < Θ) :
    ¬L.CongestedEq Θ :=
  L.clamp_no_congestedEq L.h_le_Amax hσ

/-- Pin of the sound direction on the stylized loop: `σ = 1·5 = 5` sits below
the threshold `6`, so no congested equilibrium exists there. -/
theorem signature_lt_no_congestedEq_pin :
    ¬(stepLoop 1 6 5 (by norm_num) (by norm_num)).CongestedEq 6 :=
  (stepLoop 1 6 5 (by norm_num)
    (by norm_num)).toBoundedLoop.signature_lt_no_congestedEq
      (show (1 : ℝ) * 5 < 6 by norm_num)

end BoundedLoop

/-- A loop predicate *factors through the signature* when it is constant on
signature fibers: loops of equal `σ = λ·Amax` receive the same verdict.
This is the precise sense in which a certificate reads only the exported
number — by `factorsThroughSignature_iff`, exactly the predicates of the
form `Q ∘ signature` for some `Q : ℝ → Prop`, however `Q` is chosen. -/
def FactorsThroughSignature (P : ClosedLoop → Prop) : Prop :=
  ∀ L₁ L₂ : ClosedLoop, L₁.signature = L₂.signature → (P L₁ ↔ P L₂)

/-- Factoring through the signature is exactly fiber-constancy: `P` is of
the form `Q ∘ signature` for some `Q : ℝ → Prop` iff loops of equal
signature receive the same verdict. The bridge between the definitional
form and the "reads only the exported number" reading. -/
theorem factorsThroughSignature_iff {P : ClosedLoop → Prop} :
    FactorsThroughSignature P ↔
      ∃ Q : ℝ → Prop, ∀ L : ClosedLoop, P L ↔ Q L.signature := by
  constructor
  · intro hP
    refine ⟨fun t => ∃ L : ClosedLoop, L.signature = t ∧ P L, fun L => ?_⟩
    constructor
    · intro h
      exact ⟨L, rfl, h⟩
    · rintro ⟨L', hσ, hP'⟩
      exact (hP L' L hσ).mp hP'
  · rintro ⟨Q, hQ⟩ L₁ L₂ hσ
    rw [hQ L₁, hQ L₂, hσ]

/-- The separation principle: an equal-signature pair that a property `Φ`
separates refutes every signature-factoring certificate for `Φ` — such a
certificate must give the pair one verdict, but `Φ` does not. -/
theorem no_signature_cert_of_separating_pair {Φ : ClosedLoop → Prop}
    {L₁ L₂ : ClosedLoop} (hσ : L₁.signature = L₂.signature)
    (h₁ : Φ L₁) (h₂ : ¬Φ L₂) :
    ∀ P : ClosedLoop → Prop, FactorsThroughSignature P →
      ¬∀ L : ClosedLoop, (P L ↔ Φ L) := by
  intro P hP hall
  exact h₂ ((hall L₂).mp ((hP L₁ L₂ hσ).mp ((hall L₁).mpr h₁)))

/-- **Signature incompleteness, certificate outcome.** Split one signature
`σ = λ·A` two ways — base load `λ` amplifying to `A` behind a capacity the
envelope never reaches (`stepLoop λ C A`), or the whole envelope as base
load with no amplification (`stepLoop (λ·A) C 1`). For any threshold above
the base load and at or below the envelope, the first is safe and the
second congested, so no certificate factoring through the signature decides
safety at `Θ`: `σ` forgets how demand splits between base load and
amplification headroom. Read with `signature_lt_no_congestedEq`: `σ < Θ`
certifies safety, but no reading of `σ` — however chosen — is complete. -/
theorem signature_not_decide_congestedEq {lam A C Θ : ℝ}
    (hlam : 0 < lam) (hA : 1 ≤ A) (hΘlo : lam < Θ) (hΘhi : Θ ≤ lam * A)
    (hC : lam * A < C) :
    ∀ P : ClosedLoop → Prop, FactorsThroughSignature P →
      ¬∀ L : ClosedLoop, (P L ↔ ¬L.CongestedEq Θ) := by
  have hlam' : (0 : ℝ) ≤ lam := le_of_lt hlam
  have hlamA : (0 : ℝ) ≤ lam * A := mul_nonneg hlam.le (zero_le_one.trans hA)
  refine no_signature_cert_of_separating_pair
    (L₁ := stepLoop lam C A hlam' hA)
    (L₂ := stepLoop (lam * A) C 1 hlamA le_rfl) ?_ ?_ ?_
  · change lam * A = lam * A * 1
    ring
  · rintro ⟨Λ, _, hfix, hΘΛ⟩
    rcases lt_or_ge Λ C with hΛC | hΛC
    · rw [stepLoop_F_of_lt hlam' hA hΛC] at hfix
      linarith
    · rw [stepLoop_F_of_ge hlam' hA hΛC] at hfix
      linarith
  · refine not_not_intro ⟨lam * A, hlamA, ?_, hΘhi⟩
    rw [stepLoop_F_of_lt hlamA le_rfl hC]

/-- The flat split has one candidate equilibrium: with no amplification
headroom (`A = 1`) the demand is the base load at every load level,
whatever the kernel branch, so every fixed point of `stepLoop λ C 1` is
`λ` itself. -/
theorem flat_split_fixedPt_unique {lam C : ℝ} (hlam : 0 ≤ lam) {z : ℝ}
    (hz : Function.IsFixedPt (stepLoop lam C 1 hlam le_rfl).F z) :
    z = lam := by
  have hz' : (stepLoop lam C 1 hlam le_rfl).F z = z := hz
  rcases lt_or_ge z C with hzC | hzC
  · rw [stepLoop_F_of_lt hlam le_rfl hzC] at hz'
    linarith
  · rw [stepLoop_F_of_ge hlam le_rfl hzC] at hz'
    linarith

/-!
## The band regime: congestion agrees, the phase splits
-/

/-- **In-band agreement.** Inside the band both splits of one signature are
congested at the capacity threshold: the threshold split by the band
theorem (`stepLoop_congestedEq`), the flat split because its constant
demand `λ·A` already sits at or above `C`. -/
theorem band_pair_both_congestedEq {lam A C : ℝ} (hlam : 0 < lam)
    (hA : 1 ≤ A) (hlamA : 0 ≤ lam * A) (hband_lo : C ≤ lam * A) :
    (stepLoop lam C A (le_of_lt hlam) hA).CongestedEq C ∧
      (stepLoop (lam * A) C 1 hlamA le_rfl).CongestedEq C := by
  refine ⟨stepLoop_congestedEq hlam hA hband_lo,
    lam * A, hlamA, ?_, hband_lo⟩
  rw [stepLoop_F_of_ge hlamA le_rfl hband_lo, mul_one]

/-- **In-band divergence.** The same pair differs in phase structure: the
threshold split holds two distinct equilibria while every equilibrium of
the flat split is the single point `λ·A`
(`flat_split_fixedPt_unique`). Read with `band_pair_both_congestedEq`:
congestion agreement does not extend to the phase — the split that
`signature_not_decide_two_fixedPts` turns against the certificate class. -/
theorem band_pair_phase_divergent {lam A C : ℝ} (hlam : 0 < lam)
    (hA : 1 ≤ A) (hlamA : 0 ≤ lam * A) (hband_lo : C ≤ lam * A)
    (hband_hi : lam < C) :
    (∃ z₁ z₂,
        Function.IsFixedPt (stepLoop lam C A (le_of_lt hlam) hA).F z₁ ∧
          Function.IsFixedPt (stepLoop lam C A (le_of_lt hlam) hA).F z₂ ∧
          z₁ < z₂) ∧
      ¬∃ z₁ z₂,
        Function.IsFixedPt (stepLoop (lam * A) C 1 hlamA le_rfl).F z₁ ∧
          Function.IsFixedPt (stepLoop (lam * A) C 1 hlamA le_rfl).F z₂ ∧
          z₁ < z₂ := by
  constructor
  · obtain ⟨z₁, z₂, h₁, h₂, _, _, hlt⟩ :=
      stepLoop_two_fixedPts hlam hA hband_lo hband_hi
    exact ⟨z₁, z₂, h₁, h₂, hlt⟩
  · rintro ⟨z₁, z₂, h₁, h₂, hlt⟩
    rw [flat_split_fixedPt_unique hlamA h₁,
      flat_split_fixedPt_unique hlamA h₂] at hlt
    exact lt_irrefl _ hlt

/-- **Signature incompleteness, phase structure.** Inside the band
(`λ < C ≤ λ·A`) the threshold split of a signature holds two distinct
equilibria (`stepLoop_two_fixedPts`) while the flat split of the same
signature cannot hold two (`flat_split_fixedPt_unique`), so no certificate
factoring through the signature decides the two-equilibria property. -/
theorem signature_not_decide_two_fixedPts {lam A C : ℝ}
    (hlam : 0 < lam) (hA : 1 ≤ A) (hband_lo : C ≤ lam * A)
    (hband_hi : lam < C) :
    ∀ P : ClosedLoop → Prop, FactorsThroughSignature P →
      ¬∀ L : ClosedLoop,
        (P L ↔ ∃ z₁ z₂, Function.IsFixedPt L.F z₁ ∧
          Function.IsFixedPt L.F z₂ ∧ z₁ < z₂) := by
  have hlam' : (0 : ℝ) ≤ lam := le_of_lt hlam
  have hlamA : (0 : ℝ) ≤ lam * A := mul_nonneg hlam.le (zero_le_one.trans hA)
  have hpair := band_pair_phase_divergent hlam hA hlamA hband_lo hband_hi
  refine no_signature_cert_of_separating_pair
    (L₁ := stepLoop lam C A hlam' hA)
    (L₂ := stepLoop (lam * A) C 1 hlamA le_rfl) ?_ hpair.1 hpair.2
  change lam * A = lam * A * 1
  ring

/-!
## The concrete equal-signature pair
-/

/-- The equal-signature pair, headroom side: base load `1`, response
climbing to `4`, capacity `5` — demand never reaches capacity (`F ≤ 4 < 5`
on both kernel branches), so the loop is safe at threshold `3`
(`headroomLoop_no_congestedEq`). Signature `σ = 1·4 = 4`. -/
noncomputable abbrev headroomLoop : ClosedLoop :=
  stepLoop 1 5 4 (by norm_num) (by norm_num)

/-- The equal-signature pair, flat side: base load `4`, no amplification,
same capacity — demand is `4` at every load. Signature `σ = 4·1 = 4`. -/
noncomputable abbrev flatLoop : ClosedLoop :=
  stepLoop 4 5 1 (by norm_num) (by norm_num)

/-- The pair carries one signature: `σ = 4` on both sides. -/
theorem headroomLoop_signature_eq_flatLoop :
    headroomLoop.signature = flatLoop.signature := by
  change (1 : ℝ) * 4 = 4 * 1
  norm_num

/-- The headroom side is safe at threshold `3`: below capacity its demand
is `1 < 3`, and at or above capacity its demand `4` falls short of the
capacity `5`, so no fixed point sits at or above `3`. -/
theorem headroomLoop_no_congestedEq : ¬headroomLoop.CongestedEq 3 := by
  rintro ⟨Λ, _, hfix, hΘΛ⟩
  rcases lt_or_ge Λ 5 with hΛC | hΛC
  · rw [stepLoop_F_of_lt (by norm_num) (by norm_num) hΛC] at hfix
    linarith
  · rw [stepLoop_F_of_ge (by norm_num) (by norm_num) hΛC] at hfix
    norm_num at hfix
    linarith

/-- The flat side is congested at the same threshold: `4` is a fixed point
at or above `3`. -/
theorem flatLoop_congestedEq : flatLoop.CongestedEq 3 := by
  refine ⟨4, by norm_num, ?_, by norm_num⟩
  rw [stepLoop_F_of_lt (by norm_num) (by norm_num)
    (by norm_num : (4 : ℝ) < 5)]

/-- **Non-vacuity.** The concrete pair realizes the incompleteness: equal
signature (`headroomLoop_signature_eq_flatLoop`), divergent outcome
(`headroomLoop_no_congestedEq` vs `flatLoop_congestedEq`), so no
signature-factoring certificate decides safety at `3`. -/
theorem signature_gap_witnessed :
    ∀ P : ClosedLoop → Prop, FactorsThroughSignature P →
      ¬∀ L : ClosedLoop, (P L ↔ ¬L.CongestedEq 3) :=
  no_signature_cert_of_separating_pair headroomLoop_signature_eq_flatLoop
    headroomLoop_no_congestedEq (not_not_intro flatLoop_congestedEq)

/-- Numeric regression: `signature_not_decide_congestedEq` instantiated at
`λ = 1`, `A = 4`, `C = 5`, `Θ = 3` (`1 < 3 ≤ 4 < 5`) — no
signature-factoring certificate decides safety at threshold `3` here. The
loop at these parameters is the safe leg; the congested witness inside the
proof is its equal-signature twin with `λ = 4`, `A = 1`. -/
theorem signature_not_decide_congestedEq_three :
    ∀ P : ClosedLoop → Prop, FactorsThroughSignature P →
    ¬∀ L : ClosedLoop, (P L ↔ ¬L.CongestedEq 3) :=
  signature_not_decide_congestedEq (lam := 1) (A := 4) (C := 5) (Θ := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Numeric regression: the phase form is inhabited inside the band at
`λ = 1`, `A = 4`, `C = 3`. -/
theorem signature_not_decide_two_fixedPts_three :
    ∀ P : ClosedLoop → Prop, FactorsThroughSignature P →
    ¬∀ L : ClosedLoop,
      (P L ↔ ∃ z₁ z₂, Function.IsFixedPt L.F z₁ ∧
        Function.IsFixedPt L.F z₂ ∧ z₁ < z₂) :=
  signature_not_decide_two_fixedPts (lam := 1) (A := 4) (C := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Numeric regression: the band form is inhabited inside the band at
`λ = 1`, `A = 4`, `C = 3` — the equal-signature pair both congest at `3`. -/
theorem band_pair_both_congestedEq_three :
    (stepLoop 1 3 4 (by norm_num) (by norm_num)).CongestedEq 3 ∧
      (stepLoop (1 * 4) 3 1 (by norm_num) le_rfl).CongestedEq 3 :=
  band_pair_both_congestedEq (lam := 1) (A := 4) (C := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Overload
