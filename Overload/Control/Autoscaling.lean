module

public import Overload.Basic -- shake: keep
public import Overload.Stack.Tightness
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
# Autoscaling: certify at the scaled-in floor

The practitioner argument that used to be prose, mechanized. Capacity
enters a closed loop twice — as the congestion threshold and inside the
failure kernel — and safety is monotone in both:

* Threshold side: raising the threshold only shrinks the congested set
  (`CongestedEq.mono`, contrapositive).
* Kernel side: a higher-capacity kernel fails pointwise less, and a
  congested equilibrium under the pointwise-smaller kernel is a postfixed
  point of the reference loop, so it transfers back
  (`congestedEq_mono_kernel` — the kernel-side mirror of
  `congestedEq_mono_lam`).

Combined, `ClosedLoop.floor_certifies`: certify the loop at the minimum
capacity the autoscaler can reach, and every capacity it will ever
provide is certified with it. Concretely, the step kernel is antitone
in capacity (`stepKernel_anti_capacity`), so the stylized and
truncated-geometric loops inherit the floor theorem with capacity in both
positions at once (`stepLoop_floor_certifies`,
`cappedLoop_floor_certifies`).

The bound that remains is modeling, not mathematics: everything here
holds offered load fixed — these are statements for peak `λ` against the
floor capacity, so a floor sized only for trough load certifies nothing.
The autoscaler as a *feedback controller* (reactions on lagged or
miscoded signals) is deliberately not modeled; the `Observability.lean`
theorems carry that lesson.
-/

@[expose] public section

namespace Overload

namespace ClosedLoop

variable (L : ClosedLoop)

/-- **Congestion transfers up the kernel order** — the kernel-side mirror
of `congestedEq_mono_lam`: a congested equilibrium under a
pointwise-smaller kernel (fewer failures, e.g. more capacity) is a
postfixed point of the reference loop, and Knaster–Tarski re-supplies a
genuine equilibrium above it. Contrapositive: safety of the reference
loop covers every smaller-kernel sibling. -/
theorem congestedEq_mono_kernel {g' : ℝ → ℝ}
    (hg'_mem : ∀ x, 0 ≤ x → g' x ∈ Set.Icc (0 : ℝ) 1)
    (hg'_mono : MonotoneOn g' (Set.Ici (0 : ℝ)))
    (hle : ∀ x, 0 ≤ x → g' x ≤ L.g x) {Θ : ℝ}
    (hcong : (L.withKernel g' hg'_mem hg'_mono).CongestedEq Θ) :
    L.CongestedEq Θ := by
  obtain ⟨Λ, hΛ0, hfix, hΘΛ⟩ := hcong
  have hpost : Λ ≤ L.F Λ :=
    calc Λ = L.lam * L.h (g' Λ) := hfix.symm
      _ ≤ L.lam * L.h (L.g Λ) :=
        mul_le_mul_of_nonneg_left
          (L.h_mono (hg'_mem Λ hΛ0) (L.g_mem Λ hΛ0) (hle Λ hΛ0))
          L.lam_nonneg
      _ = L.F Λ := rfl
  exact (L.congestedEq_of_inflow hΛ0 hpost).mono hΘΛ

/-- **Certify at the scaled-in floor, general form.** Safety of the
reference loop at threshold `Θ` extends to any pointwise-smaller kernel
at any higher threshold — both ways capacity helps, in one statement.
Read `L` as the loop at the floor capacity: the kernel replacement is the
higher-capacity kernel, the threshold bump is the higher capacity as the
congestion bar. -/
theorem floor_certifies {g' : ℝ → ℝ}
    (hg'_mem : ∀ x, 0 ≤ x → g' x ∈ Set.Icc (0 : ℝ) 1)
    (hg'_mono : MonotoneOn g' (Set.Ici (0 : ℝ)))
    (hle : ∀ x, 0 ≤ x → g' x ≤ L.g x) {Θ Θ' : ℝ} (hΘ : Θ ≤ Θ')
    (hsafe : ¬L.CongestedEq Θ) :
    ¬(L.withKernel g' hg'_mem hg'_mono).CongestedEq Θ' :=
  fun hcong => hsafe
    (L.congestedEq_mono_kernel hg'_mem hg'_mono hle (hcong.mono hΘ))

end ClosedLoop

/-- More capacity, fewer failures: the step kernel is antitone in its
capacity parameter, pointwise. -/
theorem stepKernel_anti_capacity {C C' : ℝ} (hCC' : C ≤ C') (x : ℝ) :
    stepKernel C' x ≤ stepKernel C x := by
  by_cases hx : x < C'
  · by_cases hxC : x < C
    · rw [stepKernel_of_lt hx, stepKernel_of_lt hxC]
    · rw [stepKernel_of_lt hx, stepKernel_of_ge (not_lt.mp hxC)]
      norm_num
  · rw [stepKernel_of_ge (not_lt.mp hx),
      stepKernel_of_ge (hCC'.trans (not_lt.mp hx))]

/-- Kernel surgery commutes with the stylized constructor: re-capacitating
a `stepLoop` is a `stepLoop`. -/
theorem stepLoop_withKernel {lam C C' A : ℝ} (hlam : 0 ≤ lam)
    (hA : 1 ≤ A) :
    (stepLoop lam C A hlam hA).withKernel (stepKernel C')
      (stepKernel_mem C') (stepKernel_monoOn C')
      = stepLoop lam C' A hlam hA := rfl

/-- Kernel surgery commutes with the truncated-geometric constructor. -/
theorem cappedLoop_withKernel {lam C C' : ℝ} {m : ℕ} (hlam : 0 ≤ lam)
    (hm : 1 ≤ m) :
    (cappedLoop lam C m hlam hm).withKernel (stepKernel C')
      (stepKernel_mem C') (stepKernel_monoOn C')
      = cappedLoop lam C' m hlam hm := rfl

/-- Congestion at a higher capacity transfers down to any lower capacity
of the stylized loop — capacity read in both positions (kernel and
threshold) at once. -/
theorem stepLoop_congestedEq_anti_capacity {lam C C' A : ℝ}
    (hlam : 0 ≤ lam) (hA : 1 ≤ A) (hCC' : C ≤ C')
    (hcong : (stepLoop lam C' A hlam hA).CongestedEq C') :
    (stepLoop lam C A hlam hA).CongestedEq C := by
  have h1 := hcong.mono hCC'
  rw [← stepLoop_withKernel hlam hA] at h1
  exact (stepLoop lam C A hlam hA).congestedEq_mono_kernel
    (stepKernel_mem C') (stepKernel_monoOn C')
    (fun x _ => stepKernel_anti_capacity hCC' x) h1

/-- **The scaled-in floor, stylized loop.** Certified safe at the floor
capacity ⟹ certified safe at every capacity the autoscaler will ever
provide — scaling up only adds margin. Offered load is held fixed: this
is a statement for peak `λ` against the floor. -/
theorem stepLoop_floor_certifies {lam Cfloor C' A : ℝ} (hlam : 0 ≤ lam)
    (hA : 1 ≤ A) (hfloor : Cfloor ≤ C')
    (hsafe : ¬(stepLoop lam Cfloor A hlam hA).CongestedEq Cfloor) :
    ¬(stepLoop lam C' A hlam hA).CongestedEq C' :=
  fun hcong =>
    hsafe (stepLoop_congestedEq_anti_capacity hlam hA hfloor hcong)

/-- Congestion at a higher capacity transfers down to any lower capacity
of the truncated-geometric loop. -/
theorem cappedLoop_congestedEq_anti_capacity {lam C C' : ℝ} {m : ℕ}
    (hlam : 0 ≤ lam) (hm : 1 ≤ m) (hCC' : C ≤ C')
    (hcong : (cappedLoop lam C' m hlam hm).CongestedEq C') :
    (cappedLoop lam C m hlam hm).CongestedEq C := by
  have h1 := hcong.mono hCC'
  rw [← cappedLoop_withKernel hlam hm] at h1
  exact (cappedLoop lam C m hlam hm).congestedEq_mono_kernel
    (stepKernel_mem C') (stepKernel_monoOn C')
    (fun x _ => stepKernel_anti_capacity hCC' x) h1

/-- **The scaled-in floor, truncated-geometric loop.** The practical form:
a retry cap certified against the floor capacity certifies the whole
autoscaling range. -/
theorem cappedLoop_floor_certifies {lam Cfloor C' : ℝ} {m : ℕ}
    (hlam : 0 ≤ lam) (hm : 1 ≤ m) (hfloor : Cfloor ≤ C')
    (hsafe : ¬(cappedLoop lam Cfloor m hlam hm).CongestedEq Cfloor) :
    ¬(cappedLoop lam C' m hlam hm).CongestedEq C' :=
  fun hcong =>
    hsafe (cappedLoop_congestedEq_anti_capacity hlam hm hfloor hcong)

/-- Numeric regression: load `1`, cap `5` certified against a floor of `6`
(`1·5 < 6`, the clamp), so capacity `100` is certified by the floor
theorem — no re-check at the larger capacity. -/
theorem cappedLoop_hundred_no_congestedEq :
    ¬(cappedLoop 1 100 5 (by norm_num) (by norm_num)).CongestedEq
    100 :=
  cappedLoop_floor_certifies (Cfloor := 6) (by norm_num) (by norm_num)
    (by norm_num) (cappedLoop_no_congestedEq (by norm_num))

/-- Numeric regression on the stylized floor form, at the same numbers: load
`1` at amplification `5` is safe against a floor of `6`, so capacity `100`
inherits the certificate. -/
theorem stepLoop_hundred_no_congestedEq :
    ¬(stepLoop 1 100 5 (by norm_num) (by norm_num)).CongestedEq 100 :=
  stepLoop_floor_certifies (Cfloor := 6) (by norm_num) (by norm_num)
    (by norm_num)
    ((stepLoop 1 6 5 (by norm_num)
      (by norm_num)).toBoundedLoop.no_congestedEq_of_light
        (show (1 : ℝ) * 5 < 6 by norm_num))

/-- Numeric regression on the general form, reaching the same capacity by
kernel surgery instead of through the stylized family: the floor certificate
transfers to the capacity-`100` kernel at the capacity-`100` threshold. -/
theorem floor_certifies_at_hundred :
    ¬((stepLoop 1 6 5 (by norm_num) (by norm_num)).withKernel (stepKernel 100)
      (stepKernel_mem 100) (stepKernel_monoOn 100)).CongestedEq 100 :=
  (stepLoop 1 6 5 (by norm_num) (by norm_num)).floor_certifies
    (stepKernel_mem 100) (stepKernel_monoOn 100)
    (fun x _ => stepKernel_anti_capacity (by norm_num) x) (by norm_num)
    ((stepLoop 1 6 5 (by norm_num)
      (by norm_num)).toBoundedLoop.no_congestedEq_of_light
        (show (1 : ℝ) * 5 < 6 by norm_num))

end Overload
