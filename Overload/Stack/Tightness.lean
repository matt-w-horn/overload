module

public import Overload.Basic -- shake: keep
public import Overload.Stack.CoupledStack
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

/-!
# Tightness: the clamp condition is exact over the kernel family

The clamp theorem (`BoundedLoop.clamp_no_congestedEq`) is a sufficient
condition consuming only the response side of a loop: `λ·K < Θ` for a clamp
`h ≤ K` removes every congested equilibrium, for any kernel. This file proves
the matching converse and makes the clamp **complete**: quantified over the
kernel — the half of the loop an operator does not control — the pointwise
clamp condition is *equivalent* to safety.

* `BoundedLoop.withKernel` / `constLoop` — kernel surgery: the same demand
  profile `(λ, h, Amax)` over a replaced kernel; the constant kernel is the
  adversarial instrument.
* `constLoop_congestedEq` — **the tightness witness**: any response level the
  profile reaches at or above the threshold is a congested equilibrium of the
  sibling loop whose kernel parks at that failure level.
* `forall_kernel_no_congestedEq_iff` — **clamp completeness**: safety for
  every kernel holds *iff* `λ·h(p) < Θ` at every failure level `p`. The
  `ClosedLoop` version restricts the adversary to monotone kernels and the
  equivalence survives — the worst kernel is constant, hence monotone.
* `coupled_budget_tight` — stack tightness: at the constant-one kernel the
  load-coupled composite attains its forced-failure envelope `λ·∏nᵢ` exactly
  (`coupledAmp_at_one`), so `coupled_budget_no_congestedEq`'s product
  premise has no slack over the kernel family.
* `spikeLoop_*` — **the fixed-kernel gap**: a loop can be safe under its own
  kernel while the pointwise clamp condition fails — and a sibling kernel
  then congests the same profile. Kernel quantification is exactly what the
  iff buys; against a *fixed* kernel the clamp stays one-directional.
-/

@[expose] public section

namespace Overload

namespace BoundedLoop

variable (L : BoundedLoop)

/-- Kernel surgery: the same demand profile `(λ, h, Amax)` over a replaced
kernel — the instrument for quantifying over "loops that differ only in the
kernel" without propositional equality of structures. -/
def withKernel (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1) : BoundedLoop :=
  { L with g := g, g_mem := hg }

/-- Kernel surgery leaves the offered load unchanged. -/
@[simp] theorem withKernel_lam (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1) :
    (L.withKernel g hg).lam = L.lam := rfl

/-- Kernel surgery leaves the response unchanged. -/
@[simp] theorem withKernel_h (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1) :
    (L.withKernel g hg).h = L.h := rfl

/-- Kernel surgery leaves the response bound unchanged. -/
@[simp] theorem withKernel_Amax (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1) :
    (L.withKernel g hg).Amax = L.Amax := rfl

/-- The demand operator after kernel surgery: same profile, new kernel. -/
@[simp] theorem withKernel_F (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1) (Λ : ℝ) :
    (L.withKernel g hg).F Λ = L.lam * L.h (g Λ) := rfl

/-- The constant kernel: failure parked at level `p₀` regardless of load —
the adversarial instrument for tightness. (`Witnesses.noRetryLoop` is its
cousin on the response side, parking `h ≡ 1` instead.) -/
def constLoop (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) : BoundedLoop :=
  L.withKernel (fun _ => p₀) (fun _ _ => hp₀)

/-- **The tightness witness.** Any nonnegative threshold at or below the
parked response `λ·h(p₀)` is a congested equilibrium threshold of the
sibling loop whose kernel parks there: `F ≡ λ·h(p₀)` is its own fixed
point. (On a bare `BoundedLoop` the response may be negative, so `0 ≤ Θ`
is load-bearing.) -/
theorem constLoop_congestedEq {p₀ Θ : ℝ} (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1)
    (hΘ0 : 0 ≤ Θ) (hΘ : Θ ≤ L.lam * L.h p₀) :
    (L.constLoop p₀ hp₀).CongestedEq Θ :=
  ⟨L.lam * L.h p₀, hΘ0.trans hΘ, rfl, hΘ⟩

/-- The pointwise clamp: strict `λ·h(p) < Θ` at every failure level removes
every congested equilibrium. The exact sufficient form the completeness
theorem inverts — no uniform clamp constant `K` needed, so it applies even
when the supremum of `h` is not attained. -/
theorem pointwise_no_congestedEq {Θ : ℝ}
    (hlt : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.lam * L.h p < Θ) :
    ¬L.CongestedEq Θ := by
  rintro ⟨Λ, hΛ0, hfix, hΘΛ⟩
  have h : L.F Λ < Θ := hlt _ (L.g_mem Λ hΛ0)
  rw [hfix] at h
  linarith

variable {L} in
/-- **Clamp completeness.** Over the kernel-quantified family — the same
demand profile `(λ, h, Amax)`, every admissible kernel — safety is
*equivalent* to the pointwise clamp condition: no kernel can congest the
profile iff `λ·h(p) < Θ` at every failure level. Converse instrument: a
level `p₀` with `λ·h(p₀) ≥ Θ` is realized as a congested equilibrium by the
constant kernel parked at `p₀` (`constLoop_congestedEq`). The clamp theorem
is not merely sufficient; against the kernel family it is exact. -/
theorem forall_kernel_no_congestedEq_iff {Θ : ℝ} (hΘ0 : 0 ≤ Θ) :
    (∀ (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1),
        ¬(L.withKernel g hg).CongestedEq Θ)
      ↔ ∀ p ∈ Set.Icc (0 : ℝ) 1, L.lam * L.h p < Θ := by
  constructor
  · intro hsafe
    by_contra hnot
    push Not at hnot
    obtain ⟨p₀, hp₀, hge⟩ := hnot
    exact hsafe (fun _ => p₀) (fun _ _ => hp₀)
      (L.constLoop_congestedEq hp₀ hΘ0 hge)
  · intro hlt g hg
    exact (L.withKernel g hg).pointwise_no_congestedEq hlt

/-- Pin of clamp completeness at the threshold where it flips. The profile
`λ = 1`, `h p = 1 + 3p` tops out at `4`: at threshold `5` the pointwise clamp
holds, so no kernel whatever can congest the profile; at threshold `4` the
clamp fails at total failure, and the iff turns that into a kernel that
does. -/
theorem forall_kernel_no_congestedEq_iff_pin :
    (∀ (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1),
        ¬((stepLoop 1 5 4 (by norm_num)
          (by norm_num)).toBoundedLoop.withKernel g hg).CongestedEq 5) ∧
      ¬∀ (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1),
        ¬((stepLoop 1 5 4 (by norm_num)
          (by norm_num)).toBoundedLoop.withKernel g hg).CongestedEq 4 := by
  refine ⟨(forall_kernel_no_congestedEq_iff (by norm_num)).mpr
    (fun p hp => ?_), fun hsafe => ?_⟩
  · change (1 : ℝ) * (1 + p * (4 - 1)) < 5
    linarith [hp.2]
  · have h1 : (1 : ℝ) * (1 + 1 * (4 - 1)) < 4 :=
      (forall_kernel_no_congestedEq_iff (by norm_num)).mp hsafe 1
        ⟨zero_le_one, le_rfl⟩
    norm_num at h1

end BoundedLoop

namespace ClosedLoop

variable (L : ClosedLoop)

/-- Kernel surgery on a closed loop: monotone-kernel replacement over the
same monotone profile. -/
def withKernel (g : ℝ → ℝ)
    (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))) : ClosedLoop where
  toBoundedLoop := L.toBoundedLoop.withKernel g hg_mem
  g_mono := hg_mono
  h_mono := L.h_mono
  h_one_le := L.h_one_le

/-- The constant kernel as a closed loop — constants are monotone, so the
adversarial instrument survives the monotone restriction. -/
def constLoop (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) : ClosedLoop :=
  L.withKernel (fun _ => p₀) (fun _ _ => hp₀) monotoneOn_const

variable {L} in
/-- **Clamp completeness, monotone class.** Restricting the adversary to
monotone kernels does not weaken it: the worst kernel is constant, hence
monotone, so safety across the monotone-kernel family is still equivalent to
the pointwise clamp condition. -/
theorem forall_kernel_no_congestedEq_iff {Θ : ℝ} (hΘ0 : 0 ≤ Θ) :
    (∀ (g : ℝ → ℝ) (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
        (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))),
        ¬(L.withKernel g hg_mem hg_mono).CongestedEq Θ)
      ↔ ∀ p ∈ Set.Icc (0 : ℝ) 1, L.lam * L.h p < Θ := by
  constructor
  · intro hsafe
    by_contra hnot
    push Not at hnot
    obtain ⟨p₀, hp₀, hge⟩ := hnot
    exact hsafe (fun _ => p₀) (fun _ _ => hp₀) monotoneOn_const
      (L.toBoundedLoop.constLoop_congestedEq hp₀ hΘ0 hge)
  · intro hlt g hg_mem hg_mono
    exact (L.withKernel g hg_mem hg_mono).pointwise_no_congestedEq hlt

/-- Pin of the monotone-class form at the same flip: restricting the adversary
to monotone kernels changes neither side. -/
theorem forall_kernel_no_congestedEq_iff_pin :
    (∀ (g : ℝ → ℝ) (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
        (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))),
        ¬((stepLoop 1 5 4 (by norm_num)
          (by norm_num)).withKernel g hg_mem hg_mono).CongestedEq 5) ∧
      ¬∀ (g : ℝ → ℝ) (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
        (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))),
        ¬((stepLoop 1 5 4 (by norm_num)
          (by norm_num)).withKernel g hg_mem hg_mono).CongestedEq 4 := by
  refine ⟨(forall_kernel_no_congestedEq_iff (by norm_num)).mpr
    (fun p hp => ?_), fun hsafe => ?_⟩
  · change (1 : ℝ) * (1 + p * (4 - 1)) < 5
    linarith [hp.2]
  · have h1 : (1 : ℝ) * (1 + 1 * (4 - 1)) < 4 :=
      (forall_kernel_no_congestedEq_iff (by norm_num)).mp hsafe 1
        ⟨zero_le_one, le_rfl⟩
    norm_num at h1

end ClosedLoop

/-- **Stack tightness.** At the constant-one kernel — total bottom failure —
the load-coupled stack composite attains its forced-failure envelope exactly
(`coupledAmp_at_one`): any threshold at or below `λ·∏nᵢ` is a congested
equilibrium. So the product premise of `coupled_budget_no_congestedEq`
(`λ·∏nᵢ < C`) cannot be weakened over the kernel family. -/
theorem coupled_budget_tight (lam : ℝ) (layers : List (ℝ × ℕ))
    (hlam : 0 ≤ lam) (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1)
    (hcap : ∀ x ∈ layers, 1 ≤ x.2) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ lam * capProd layers) :
    (coupledLoop lam (fun _ => 1) layers hlam
        (fun _ _ => ⟨zero_le_one, le_rfl⟩) monotoneOn_const hℓ
        hcap).CongestedEq C :=
  ⟨lam * capProd layers, hC0.trans hC, by
    change lam * coupledAmp layers 1 = lam * capProd layers
    rw [coupledAmp_at_one], hC⟩

/-- Pin of stack tightness at the two-layer composite's own numbers: offered
load `8` against a cap product of `4` congests at exactly `32`, the envelope
the budget premise has to clear. -/
theorem coupled_budget_tight_pin :
    (coupledLoop 8 (fun _ => 1) [((1 / 2 : ℝ), 2), ((1 / 2 : ℝ), 2)]
      (by norm_num) (fun _ _ => ⟨zero_le_one, le_rfl⟩) monotoneOn_const
      twoLayer_mem twoLayer_cap).CongestedEq 32 :=
  coupled_budget_tight 8 _ (by norm_num) twoLayer_mem twoLayer_cap
    (by norm_num) (by norm_num [capProd_cons, capProd_nil])

/-!
## The fixed-kernel gap

Against a *fixed* kernel the pointwise clamp condition is not necessary:
the spike profile below is safe under its own kernel (which never lands
where the response spikes) even though the condition fails — and the
constant kernel parked at the spike congests the very same profile. The
kernel quantification in `forall_kernel_no_congestedEq_iff` is therefore
exactly what completeness costs.
-/

/-- The fixed-kernel gap witness: the `stepLoop 1 1 4` demand profile
(`h p = 1 + 3p`, offered load `1`) with its kernel parked at zero — failures
never materialize, whatever the load. (The `stepLoop` capacity argument is
irrelevant after the kernel surgery.) -/
noncomputable abbrev spikeLoop : ClosedLoop :=
  (stepLoop 1 1 4 (by norm_num) (by norm_num)).constLoop 0
    ⟨le_rfl, zero_le_one⟩

/-- Under its own kernel the spike profile is safe: the kernel never lands
where the response spikes, so the only equilibrium is the offered load
`1 < 3`. -/
theorem spikeLoop_no_congestedEq : ¬spikeLoop.CongestedEq 3 := by
  rintro ⟨Λ, hΛ0, hfix, hΘΛ⟩
  rw [(ClosedLoop.blip_unique_eq (L := spikeLoop) (p₀ := 0) (fun _ _ => rfl)
    hΛ0).mp hfix,
    show spikeLoop.lam * spikeLoop.h 0 = (1 : ℝ) * (1 + 0 * (4 - 1)) from rfl]
    at hΘΛ
  norm_num at hΘΛ

/-- The pointwise clamp condition fails for the spike profile: at total
failure the response reaches `1·h(1) = 4 ≥ 3`. -/
theorem spikeLoop_pointwise_fails :
    ¬∀ p ∈ Set.Icc (0 : ℝ) 1, spikeLoop.lam * spikeLoop.h p < 3 := by
  intro h
  have h4 : (1 : ℝ) * (1 + 1 * (4 - 1)) < 3 := h 1 ⟨zero_le_one, le_rfl⟩
  norm_num at h4

/-- The same profile congests under a sibling kernel: parked at total
failure instead of none, the spike profile holds a congested equilibrium at
the same threshold. Read with `spikeLoop_no_congestedEq` and
`spikeLoop_pointwise_fails`: safety under one kernel certifies nothing about
the profile's other kernels — only the pointwise clamp condition does. -/
theorem spikeLoop_sibling_congestedEq :
    (spikeLoop.toBoundedLoop.constLoop 1
      ⟨zero_le_one, le_rfl⟩).CongestedEq 3 := by
  refine spikeLoop.toBoundedLoop.constLoop_congestedEq _ (by norm_num) ?_
  change (3 : ℝ) ≤ 1 * (1 + 1 * (4 - 1))
  norm_num

end Overload
