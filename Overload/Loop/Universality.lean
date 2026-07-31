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
# Universality: the phase diagram as a function of dimensionless groups

The thesis candidate: retry systems over fixed capacity form a
universality class — the phase diagram (healthy-only, bistable, congested-only)
is a function of a small set of dimensionless groups, so two systems matching
the groups sit at the same point regardless of implementation.

What is actually proved here, precisely scoped:

* The three **phase regions** are defined by two inequalities in `(λ, A, C)`:
  `HealthyOnly` (`λ·A < C`), `BistableBand` (`λ < C ≤ λ·A`), `CongestedOnly`
  (`C ≤ λ`). `phase_trichotomy` shows they cover the parameter space; on the
  physical region `0 ≤ λ`, `1 ≤ A` the disjointness lemmas make them pairwise
  disjoint (for `A < 1`, healthy-only and congested-only can overlap — the
  regions partition only where amplification is at least one).
* Each region delivers certified dynamics, with an asymmetry stated honestly:
  the healthy-only and congested-only legs are **universal** — for *any*
  closed loop with the matching data, `BoundedLoop.no_congestedEq_of_light`
  (the congested equilibrium cannot exist) and
  `ClosedLoop.congestedEq_of_over` / `ClosedLoop.eq_ge_of_over` (an
  equilibrium exists and every equilibrium is congested). The bistable leg is
  **existential**: a band position makes bistability possible, not automatic
  (a load-blind kernel in the band is monostable), and
  `bistableBand_realized` exhibits it on the stylized saturated kernel.
* **Scale invariance**: each region predicate is invariant under
  `(λ, C) ↦ (cλ, cC)`, and `phase_matches_of_rho_eq` states the transfer
  claim exactly: two systems with equal `ρ₀ = λ/C` and equal amplification `A`
  are in the same phase. Absolute capacity never matters; only the groups do.

The claim deliberately **not** made: that the groups determine cliff depth or
hysteresis width quantitatively for arbitrary kernels — that
territory is left unformalized, not a theorem here.
-/

@[expose] public section

namespace Overload

/-!
## The three phase regions
-/

/-- Healthy-only: even fully amplified demand fits under capacity. -/
def HealthyOnly (lam A C : ℝ) : Prop := lam * A < C

/-- The bistable band: fresh demand fits, amplified demand does not. -/
def BistableBand (lam A C : ℝ) : Prop := lam < C ∧ C ≤ lam * A

/-- Congested-only: fresh demand alone meets or exceeds capacity. -/
def CongestedOnly (lam C : ℝ) : Prop := C ≤ lam

/-- The three regions cover the whole parameter space. (They are pairwise
disjoint only on the physical region `0 ≤ λ`, `1 ≤ A` — see the disjointness
lemmas and their hypotheses.) -/
theorem phase_trichotomy (lam A C : ℝ) :
    HealthyOnly lam A C ∨ BistableBand lam A C ∨ CongestedOnly lam C := by
  by_cases h1 : C ≤ lam
  · exact Or.inr (Or.inr h1)
  by_cases h2 : C ≤ lam * A
  · exact Or.inr (Or.inl ⟨not_le.mp h1, h2⟩)
  · exact Or.inl (not_le.mp h2)

/-- Pin of `phase_trichotomy` at `(λ, A, C) = (3, 1/2, 2)`, taken off the
physical region `1 ≤ A` where the cover is not a partition: the healthy-only
and congested-only regions both hold there, which is what the `1 ≤ A`
hypothesis on `healthyOnly_not_congestedOnly` buys. -/
theorem phase_trichotomy_pin :
    (HealthyOnly 3 (1 / 2) 2 ∨ BistableBand 3 (1 / 2) 2 ∨ CongestedOnly 3 2) ∧
      HealthyOnly 3 (1 / 2) 2 ∧ CongestedOnly 3 2 :=
  ⟨phase_trichotomy 3 (1 / 2) 2, by unfold HealthyOnly; norm_num,
    by unfold CongestedOnly; norm_num⟩

/-- Healthy-only is disjoint from the bistable band, with no physical-region
hypothesis: amplified demand cannot both fit under capacity (`λ·A < C`) and
meet or exceed it (`C ≤ λ·A`). -/
theorem healthyOnly_not_bistable {lam A C : ℝ} (h : HealthyOnly lam A C) :
    ¬BistableBand lam A C := fun hb => absurd h (not_lt.mpr hb.2)

/-- The bistable band is disjoint from congested-only, with no
physical-region hypothesis: fresh demand cannot both fit under capacity
(`λ < C`) and meet or exceed it (`C ≤ λ`). -/
theorem bistable_not_congestedOnly {lam A C : ℝ} (h : BistableBand lam A C) :
    ¬CongestedOnly lam C := not_le.mpr h.1

/-- Healthy-only is disjoint from congested-only on the physical region
`0 ≤ λ`, `1 ≤ A`: there `λ ≤ λ·A`, so `λ·A < C` and `C ≤ λ` cannot both
hold. For `A < 1` the two regions can overlap; `phase_trichotomy_pin`
exhibits the overlap at `A = 1/2`. -/
theorem healthyOnly_not_congestedOnly {lam A C : ℝ} (hlam : 0 ≤ lam)
    (hA : 1 ≤ A) (h : HealthyOnly lam A C) : ¬CongestedOnly lam C :=
  fun hc => absurd (lt_of_lt_of_le h hc)
    (not_lt.mpr (le_mul_of_one_le_right hlam hA))

/-- Pin of the three disjointness lemmas on the physical region. At
`(λ, A, C) = (1, 2, 3)` amplified demand `2` still fits under `3`, so that
point is neither bistable nor congested-only; at `(1, 3, 2)` fresh demand `1`
fits under `2`, so that point is not congested-only. -/
theorem phase_regions_disjoint_pin :
    ¬BistableBand 1 2 3 ∧ ¬CongestedOnly 1 3 ∧ ¬CongestedOnly 1 2 := by
  have hhealthy : HealthyOnly 1 2 3 := by unfold HealthyOnly; norm_num
  have hband : BistableBand 1 3 2 := by unfold BistableBand; norm_num
  exact ⟨healthyOnly_not_bistable hhealthy,
    healthyOnly_not_congestedOnly (by norm_num) (by norm_num) hhealthy,
    bistable_not_congestedOnly hband⟩

/-!
## Each region delivers its dynamics — for any closed loop
-/

namespace BoundedLoop

/-- **Healthy-only, dynamically**: when even fully amplified demand fits
(`λ·Amax < Θ`), no congested equilibrium exists — for *any* kernel and any
amplification response under the bound. Lives on the boundedness core: the
envelope `F ≤ λ·Amax` is all the proof uses, so batching kernels and
backpressure clients inherit the healthy leg too. -/
theorem no_congestedEq_of_light (L : BoundedLoop) {Θ : ℝ}
    (h : HealthyOnly L.lam L.Amax Θ) : ¬L.CongestedEq Θ :=
  L.clamp_no_congestedEq L.h_le_Amax h

/-- Pin of the healthy leg on the stylized loop: at `λ = 1` and `A = 2` the
envelope `λ·Amax = 2` sits below the threshold `3`, so no congested
equilibrium exists there — whatever the capacity `5` does in between. -/
theorem no_congestedEq_of_light_pin :
    ¬(stepLoop 1 5 2 (by norm_num) (by norm_num)).CongestedEq 3 :=
  (stepLoop 1 5 2 (by norm_num) (by norm_num)).toBoundedLoop.no_congestedEq_of_light
    (show (1 : ℝ) * 2 < 3 by norm_num)

end BoundedLoop

namespace ClosedLoop

/-- **Congested-only, existence**: once fresh demand alone meets the
threshold (`Θ ≤ λ`), a congested equilibrium exists — for *any* kernel
(Knaster–Tarski supplies the fixed point, and every fixed point sits at or
above the offered load). -/
theorem congestedEq_of_over (L : ClosedLoop) {Θ : ℝ}
    (hover : CongestedOnly L.lam Θ) : L.CongestedEq Θ := by
  have hA0 : (0 : ℝ) ≤ L.Amax := le_trans zero_le_one L.one_le_Amax
  have hab : (0 : ℝ) ≤ L.lam * L.Amax := mul_nonneg L.lam_nonneg hA0
  have hmem := lfpIcc_mem_Icc (F := L.F) hab L.F_mapsTo
  have hfix : L.F (lfpIcc L.F 0 (L.lam * L.Amax))
      = lfpIcc L.F 0 (L.lam * L.Amax) :=
    isFixedPt_lfpIcc hab L.F_monotoneOn_Icc L.F_mapsTo
  refine ⟨lfpIcc L.F 0 (L.lam * L.Amax), hmem.1, hfix, ?_⟩
  calc Θ ≤ L.lam := hover
    _ ≤ L.F (lfpIcc L.F 0 (L.lam * L.Amax)) := L.lam_le_F hmem.1
    _ = lfpIcc L.F 0 (L.lam * L.Amax) := hfix

/-- **The degenerate threshold, disclosed.** At a nonpositive threshold every
closed loop has a congested equilibrium: `Θ ≤ 0 ≤ lam` places the loop in the
congested-only region, so `congestedEq_of_over` applies with no hypothesis on
the loop at all. `BoundedLoop.CongestedEq` is deliberately left unguarded, so
this theorem is the disclosure — the predicate carries content only at
`0 < Θ`. -/
theorem congestedEq_of_nonpos_threshold (L : ClosedLoop) {Θ : ℝ}
    (hΘ : Θ ≤ 0) : L.CongestedEq Θ :=
  L.congestedEq_of_over (hΘ.trans L.lam_nonneg)

/-- Pin of the degenerate threshold: the stylized loop at load `1` under
capacity `5` — as healthy as a loop gets — still satisfies `CongestedEq 0`. -/
theorem congestedEq_of_nonpos_threshold_pin :
    (stepLoop 1 5 2 (by norm_num) (by norm_num)).CongestedEq 0 :=
  (stepLoop 1 5 2 (by norm_num) (by norm_num)).congestedEq_of_nonpos_threshold le_rfl

/-- **Congested-only, exhaustively**: under sustained overload every steady
state is congested — the healthy branch does not exist to recover to. This is
what distinguishes "congested-only" from merely "a congested equilibrium
exists" (the bistable band has that too). -/
theorem eq_ge_of_over (L : ClosedLoop) {Θ Λ : ℝ}
    (hover : CongestedOnly L.lam Θ) (hΛ : 0 ≤ Λ) (hfix : L.F Λ = Λ) :
    Θ ≤ Λ := by
  calc Θ ≤ L.lam := hover
    _ ≤ L.F Λ := L.lam_le_F hΛ
    _ = Λ := hfix

/-- Pin of `eq_ge_of_over` at concrete numbers (the inequality itself is
immediate; the content is the route). `stepLoop 20 10 5` is congested-only at
threshold `10` (`CongestedOnly 20 10` is `10 ≤ 20`), and `Λ = 100 = λ·A` is a
fixed point (`F 100 = 20·5`); the theorem places it at or above the
threshold. -/
theorem eq_ge_of_over_pin : (10 : ℝ) ≤ 100 :=
  (stepLoop 20 10 5 (by norm_num) (by norm_num)).eq_ge_of_over
    (show (10 : ℝ) ≤ 20 by norm_num) (by norm_num)
    (by rw [stepLoop_F_of_ge (by norm_num) (by norm_num) (by norm_num)]; norm_num)

end ClosedLoop

/-- **The band is realized.** Inside the bistable band the stylized saturated
loop actually exhibits the order gap (and `stepLoop_two_fixedPts` upgrades it
to two genuine equilibria). Unlike the other two regions this leg is
existential: a band position makes bistability *possible*, not universal — a
load-blind kernel in the band is monostable. -/
theorem bistableBand_realized {lam A C : ℝ} (hband : BistableBand lam A C)
    (hlam : 0 < lam) (hA : 1 ≤ A) :
    BistableOn (stepLoop lam C A (le_of_lt hlam) hA).F 0 (lam * A) :=
  stepLoop_bistable hlam hA hband.2 hband.1

/-- Pin of the band realization at `(λ, A, C) = (1, 2, 3/2)`: fresh demand `1`
fits under `3/2` and amplified demand `2` does not, so the stylized loop shows
the order gap on `[0, 2]`. -/
theorem bistableBand_realized_pin :
    BistableOn (stepLoop 1 (3 / 2) 2 (by norm_num) (by norm_num)).F 0 (1 * 2) :=
  bistableBand_realized (by unfold BistableBand; norm_num) (by norm_num) (by norm_num)

/-!
## Scale invariance: the phase is a function of the groups alone
-/

/-- Healthy-only is invariant under `(λ, C) ↦ (cλ, cC)` for `0 < c`. -/
theorem healthyOnly_scale {lam A C c : ℝ} (hc : 0 < c) :
    HealthyOnly (c * lam) A (c * C) ↔ HealthyOnly lam A C := by
  unfold HealthyOnly
  rw [mul_assoc]
  exact mul_lt_mul_iff_right₀ hc

/-- The bistable band is invariant under `(λ, C) ↦ (cλ, cC)` for `0 < c`. -/
theorem bistableBand_scale {lam A C c : ℝ} (hc : 0 < c) :
    BistableBand (c * lam) A (c * C) ↔ BistableBand lam A C := by
  unfold BistableBand
  rw [mul_assoc]
  exact and_congr (mul_lt_mul_iff_right₀ hc) (mul_le_mul_iff_right₀ hc)

/-- Congested-only is invariant under `(λ, C) ↦ (cλ, cC)` for `0 < c`. -/
theorem congestedOnly_scale {lam C c : ℝ} (hc : 0 < c) :
    CongestedOnly (c * lam) (c * C) ↔ CongestedOnly lam C := by
  unfold CongestedOnly
  exact mul_le_mul_iff_right₀ hc

/-- Pin of the three scale invariances at `c = 2`: the healthy-only point
`(1, 2, 3)`, the band point `(1, 3, 2)`, and the congested-only point
`(3, 1)` each keep their phase when load and capacity double. -/
theorem phase_scale_pin :
    HealthyOnly (2 * 1) 2 (2 * 3) ∧ BistableBand (2 * 1) 3 (2 * 2) ∧
      CongestedOnly (2 * 3) (2 * 1) :=
  ⟨(healthyOnly_scale (by norm_num)).mpr (by unfold HealthyOnly; norm_num),
    (bistableBand_scale (by norm_num)).mpr (by unfold BistableBand; norm_num),
    (congestedOnly_scale (by norm_num)).mpr (by unfold CongestedOnly; norm_num)⟩

/-- Healthy-only in group coordinates: `ρ₀·A < 1` where `ρ₀ = λ/C`. -/
theorem healthyOnly_iff_rho {lam A C : ℝ} (hC : 0 < C) :
    HealthyOnly lam A C ↔ lam / C * A < 1 := by
  unfold HealthyOnly
  rw [div_mul_eq_mul_div, div_lt_one hC]

/-- The bistable band in group coordinates: `ρ₀ < 1 ≤ ρ₀·A`. -/
theorem bistableBand_iff_rho {lam A C : ℝ} (hC : 0 < C) :
    BistableBand lam A C ↔ lam / C < 1 ∧ 1 ≤ lam / C * A := by
  unfold BistableBand
  rw [div_lt_one hC, div_mul_eq_mul_div, le_div_iff₀ hC, one_mul]

/-- Congested-only in group coordinates: `1 ≤ ρ₀`. -/
theorem congestedOnly_iff_rho {lam C : ℝ} (hC : 0 < C) :
    CongestedOnly lam C ↔ 1 ≤ lam / C := by
  unfold CongestedOnly
  rw [le_div_iff₀ hC, one_mul]

/-- The band edges in load coordinates: `λ ∈ [C/A, C)` — the
`(C/A_cong, C)` band, with the closed lower edge made explicit. -/
theorem bistableBand_iff_edges {lam A C : ℝ} (hA : 0 < A) :
    BistableBand lam A C ↔ C / A ≤ lam ∧ lam < C := by
  unfold BistableBand
  rw [div_le_iff₀ hA, and_comm]

/-- **The transfer claim, exactly**: two systems with equal `ρ₀ = λ/C` and
equal amplification group `A` occupy the same phase — regardless of their
absolute loads and capacities. This is the precise sense in which the phase
classification factors through the dimensionless groups. -/
theorem phase_matches_of_rho_eq {lam₁ C₁ lam₂ C₂ A : ℝ} (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hrho : lam₁ / C₁ = lam₂ / C₂) :
    (HealthyOnly lam₁ A C₁ ↔ HealthyOnly lam₂ A C₂) ∧
    (BistableBand lam₁ A C₁ ↔ BistableBand lam₂ A C₂) ∧
    (CongestedOnly lam₁ C₁ ↔ CongestedOnly lam₂ C₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [healthyOnly_iff_rho hC₁, healthyOnly_iff_rho hC₂, hrho]
  · rw [bistableBand_iff_rho hC₁, bistableBand_iff_rho hC₂, hrho]
  · rw [congestedOnly_iff_rho hC₁, congestedOnly_iff_rho hC₂, hrho]

/-- Pin of the transfer claim: `(λ, C) = (1, 2)` and `(5, 10)` share
`ρ₀ = 1/2`, so the band membership of the small system carries to the large
one at the same amplification `A = 3` — capacity ten times over, same phase. -/
theorem phase_matches_of_rho_eq_pin : BistableBand 5 3 10 :=
  (phase_matches_of_rho_eq (lam₁ := 1) (C₁ := 2) (lam₂ := 5) (C₂ := 10) (A := 3)
    (by norm_num) (by norm_num) (by norm_num)).2.1.mp
      (by unfold BistableBand; norm_num)

end Overload
