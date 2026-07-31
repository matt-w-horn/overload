module

public import Overload.Basic -- shake: keep
public import Overload.Loop.Universality
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
# Hysteresis: equilibrium selection under a load sweep

The bistable band holds two equilibria; which one a
system occupies depends on where it came from — collapse at the band's upper
edge, recovery only at its lower edge. This file proves the order-theoretic
core of that story, with no dynamics beyond monotone iteration:

* `ClosedLoop.withLam` — demand-level surgery: the same mechanism `(g, h)`
  swept across offered loads.
* `lfpIcc_mono_lam` / `gfpIcc_mono_lam` — **equilibria move monotonically in
  offered load** (via `lfpIcc_mono_of_le`/`gfpIcc_mono_of_le`): raising `λ`
  never lowers either extremal equilibrium.
* `congestedEq_mono_lam` / `not_congestedEq_of_le` — **the congested set is
  an up-set in `λ`**: collapse persists under rising load, and safety at a
  high load certifies every lower load. `congestionEdge` names the least
  congesting load as an infimum, with two-sided bounds; attainment at the
  edge is not claimed in general, and on the stylized loop the edge
  evaluates exactly: `congestionEdge = C/A` (`stepLoop_congestionEdge`).
* `stepLoop_lfpIcc_of_lt` / `stepLoop_gfpIcc_of_ge` /
  `stepLoop_gfpIcc_of_healthyOnly` / `stepLoop_lfpIcc_of_ge` — closed forms
  for both extremal equilibria of the stylized loop in every phase region,
  packaged as `stepLoop_equilibrium_trichotomy`.
* `stepLoop_jump_up` / `stepLoop_jump_down` — **the hysteresis loop**: the
  healthy branch tracks `λ` until the upper edge `C` and jumps by `C·(A−1)`;
  the congested branch holds `λ·A` down to the lower edge `C/A` (where it
  still sustains exactly `C`) and only then collapses to `λ`. Collapse and
  recovery happen at *different* loads — path dependence in equilibrium
  selection.
* `stepLoop_sweep_up_le` — the upward sweep from empty never overshoots the
  healthy equilibrium (`iterate_le_lfpIcc`). Sweep *dynamics* — rates,
  jitter, trajectories — remain simulator territory; these are the
  order-theoretic endpoints any sweep must respect.
-/

@[expose] public section

namespace Overload

namespace BoundedLoop

/-- Threshold weakening: congestion at a higher threshold is congestion at
any lower one. -/
theorem CongestedEq.mono {L : BoundedLoop} {Θ Θ' : ℝ}
    (h : L.CongestedEq Θ') (hΘ : Θ ≤ Θ') : L.CongestedEq Θ :=
  let ⟨Λ, hΛ0, hfix, hΘ'Λ⟩ := h
  ⟨Λ, hΛ0, hfix, hΘ.trans hΘ'Λ⟩

end BoundedLoop

namespace ClosedLoop

variable (L : ClosedLoop)

/-- The invariance interval, generalized endpoint: any ceiling at or above
the demand envelope `λ·Amax` is invariant (`F_mapsTo` is the tight case).
Two-loop comparisons need a *common* interval, which this supplies. -/
theorem F_mapsTo_of_le {b : ℝ} (hb : L.lam * L.Amax ≤ b) :
    Set.MapsTo L.F (Set.Icc 0 b) (Set.Icc 0 b) :=
  fun _x hx => ⟨L.F_nonneg hx.1, (L.F_le hx.1).trans hb⟩

/-- Demand-level surgery: the same mechanism — kernel and response — at a
different offered load. The instrument for sweeping `λ` while holding the
system fixed. -/
def withLam (lam' : ℝ) (hlam' : 0 ≤ lam') : ClosedLoop :=
  { L with lam := lam', lam_nonneg := hlam' }

/-- Demand-level surgery sets the offered load. -/
@[simp] theorem withLam_lam (lam' : ℝ) (hlam' : 0 ≤ lam') :
    (L.withLam lam' hlam').lam = lam' := rfl

/-- Demand-level surgery leaves the kernel unchanged. -/
@[simp] theorem withLam_g (lam' : ℝ) (hlam' : 0 ≤ lam') :
    (L.withLam lam' hlam').g = L.g := rfl

/-- Demand-level surgery leaves the response unchanged. -/
@[simp] theorem withLam_h (lam' : ℝ) (hlam' : 0 ≤ lam') :
    (L.withLam lam' hlam').h = L.h := rfl

/-- Demand-level surgery leaves the response bound unchanged. -/
@[simp] theorem withLam_Amax (lam' : ℝ) (hlam' : 0 ≤ lam') :
    (L.withLam lam' hlam').Amax = L.Amax := rfl

/-- The demand operator after demand-level surgery. -/
theorem withLam_F (lam' : ℝ) (hlam' : 0 ≤ lam') (Λ : ℝ) :
    (L.withLam lam' hlam').F Λ = lam' * L.h (L.g Λ) := rfl

/-- Raising offered load raises demand pointwise: the loop family is
monotone in `λ`. (The response floor `1 ≤ h` supplies the sign.) -/
theorem F_le_withLam_F {lam' : ℝ} (hlam' : 0 ≤ lam') (hle : L.lam ≤ lam')
    {x : ℝ} (hx : 0 ≤ x) : L.F x ≤ (L.withLam lam' hlam').F x := by
  have hh : 0 ≤ L.h (L.g x) :=
    le_trans zero_le_one (L.h_one_le _ (L.g_mem x hx))
  exact mul_le_mul_of_nonneg_right hle hh

/-- **Equilibria move monotonically in offered load, healthy side**: on a
common interval containing both demand envelopes, the least fixed point at
the higher load dominates the one at the lower load. -/
theorem lfpIcc_mono_lam {lam' b : ℝ} (hlam' : 0 ≤ lam') (hle : L.lam ≤ lam')
    (hb : lam' * L.Amax ≤ b) :
    lfpIcc L.F 0 b ≤ lfpIcc (L.withLam lam' hlam').F 0 b := by
  have hA0 : (0 : ℝ) ≤ L.Amax := zero_le_one.trans L.one_le_Amax
  have hb0 : (0 : ℝ) ≤ b := (mul_nonneg hlam' hA0).trans hb
  exact lfpIcc_mono_of_le hb0 (fun x hx => L.F_le_withLam_F hlam' hle hx.1)
    ((L.withLam lam' hlam').F_mapsTo_of_le hb)

/-- **Equilibria move monotonically in offered load, congested side**: the
greatest fixed point at the higher load dominates the one at the lower
load. -/
theorem gfpIcc_mono_lam {lam' b : ℝ} (hlam' : 0 ≤ lam') (hle : L.lam ≤ lam')
    (hb : lam' * L.Amax ≤ b) :
    gfpIcc L.F 0 b ≤ gfpIcc (L.withLam lam' hlam').F 0 b := by
  have hA0 : (0 : ℝ) ≤ L.Amax := zero_le_one.trans L.one_le_Amax
  have hb0 : (0 : ℝ) ≤ b := (mul_nonneg hlam' hA0).trans hb
  have hbL : L.lam * L.Amax ≤ b :=
    le_trans (mul_le_mul_of_nonneg_right hle hA0) hb
  exact gfpIcc_mono_of_le hb0 (fun x hx => L.F_le_withLam_F hlam' hle hx.1)
    (L.F_mapsTo_of_le hbL)

/-- **The congested set is an up-set in offered load**: congestion at `λ`
transfers to any higher load. The congested witness is postfixed under the
larger demand operator, and Knaster–Tarski re-supplies a genuine equilibrium
above it — collapse persists as load rises. -/
theorem congestedEq_mono_lam {lam' Θ : ℝ} (hlam' : 0 ≤ lam')
    (hle : L.lam ≤ lam') (hcong : L.CongestedEq Θ) :
    (L.withLam lam' hlam').CongestedEq Θ := by
  obtain ⟨Λ₀, hΛ0, hfix, hΘΛ⟩ := hcong
  have hpost : Λ₀ ≤ (L.withLam lam' hlam').F Λ₀ :=
    calc Λ₀ = L.F Λ₀ := hfix.symm
      _ ≤ (L.withLam lam' hlam').F Λ₀ := L.F_le_withLam_F hlam' hle hΛ0
  exact ((L.withLam lam' hlam').congestedEq_of_inflow hΛ0 hpost).mono hΘΛ

/-- Dual reading: safety is a down-set in offered load — a loop safe at the
higher load was already safe at every lower one. Healthy survives lowering
`λ`. -/
theorem not_congestedEq_of_le {lam' Θ : ℝ} (hlam' : 0 ≤ lam')
    (hle : L.lam ≤ lam')
    (hsafe : ¬(L.withLam lam' hlam').CongestedEq Θ) : ¬L.CongestedEq Θ :=
  fun hcong => hsafe (L.congestedEq_mono_lam hlam' hle hcong)

/-- The congestion edge: the infimum offered load at which the mechanism
`(g, h)` sustains a congested equilibrium at threshold `Θ`. Because the
congested set is an up-set (`congestedEq_mono_lam`), this single number
splits the load axis; the results state bounds only — attainment at the
edge is never claimed. -/
noncomputable def congestionEdge (Θ : ℝ) : ℝ :=
  sInf {lam' | ∃ h : 0 ≤ lam', (L.withLam lam' h).CongestedEq Θ}

/-- Any congesting load bounds the congestion edge from above. -/
theorem congestionEdge_le {lam' Θ : ℝ} (hlam' : 0 ≤ lam')
    (hcong : (L.withLam lam' hlam').CongestedEq Θ) :
    L.congestionEdge Θ ≤ lam' :=
  csInf_le ⟨0, fun _ hx => hx.elim fun hx0 _ => hx0⟩ ⟨hlam', hcong⟩

/-- The congestion edge is at least `Θ/Amax`: below that load even the
saturated response cannot reach the threshold. The congesting set is never
empty — loading the mechanism to `max Θ 0` puts it in the congested-only
region — so no nonemptiness hypothesis is carried. -/
theorem le_congestionEdge {Θ : ℝ} :
    Θ / L.Amax ≤ L.congestionEdge Θ := by
  have hAmax0 : (0 : ℝ) < L.Amax := lt_of_lt_of_le zero_lt_one L.one_le_Amax
  have hne : {lam' | ∃ h : 0 ≤ lam',
      (L.withLam lam' h).CongestedEq Θ}.Nonempty :=
    ⟨max Θ 0, le_max_right Θ 0,
      (L.withLam (max Θ 0) (le_max_right Θ 0)).congestedEq_of_over
        (le_max_left Θ 0)⟩
  refine le_csInf hne ?_
  rintro x ⟨hx0, Λ, hΛ0, hfix, hΘΛ⟩
  have hFle : (L.withLam x hx0).F Λ ≤ x * L.Amax := (L.withLam x hx0).F_le hΛ0
  rw [hfix] at hFle
  rw [div_le_iff₀ hAmax0]
  exact hΘΛ.trans hFle

end ClosedLoop

/-- Pin of the two load-monotonicity legs on a common envelope: raising the
load from `1` to `2` against capacity `10` moves both extremal equilibria up,
read on `[0, 8]`, the interval carrying both demand envelopes. -/
theorem equilibria_mono_lam_pin :
    lfpIcc (stepLoop 1 10 4 (by norm_num) (by norm_num)).F 0 8
        ≤ lfpIcc (stepLoop 2 10 4 (by norm_num) (by norm_num)).F 0 8 ∧
      gfpIcc (stepLoop 1 10 4 (by norm_num) (by norm_num)).F 0 8
        ≤ gfpIcc (stepLoop 2 10 4 (by norm_num) (by norm_num)).F 0 8 :=
  ⟨(stepLoop 1 10 4 (by norm_num) (by norm_num)).lfpIcc_mono_lam (lam' := 2)
      (by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
      (show (2 : ℝ) * 4 ≤ 8 by norm_num),
    (stepLoop 1 10 4 (by norm_num) (by norm_num)).gfpIcc_mono_lam (lam' := 2)
      (by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
      (show (2 : ℝ) * 4 ≤ 8 by norm_num)⟩

/-- Pin of the down-set reading: the mechanism at load `2` is safe under
threshold `10` because `2·4 = 8 < 10`, so the same mechanism at load `1` was
already safe — obtained by lowering the load, not by certifying again. -/
theorem not_congestedEq_of_le_pin :
    ¬(stepLoop 1 10 4 (by norm_num) (by norm_num)).CongestedEq 10 :=
  (stepLoop 1 10 4 (by norm_num) (by norm_num)).not_congestedEq_of_le
    (lam' := 2) (by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
    (((stepLoop 1 10 4 (by norm_num) (by norm_num)).withLam 2
      (by norm_num)).toBoundedLoop.no_congestedEq_of_light
        (show (2 : ℝ) * 4 < 10 by norm_num))

/-- Demand-level surgery commutes with the stylized constructor: re-loading
a `stepLoop` is a `stepLoop`. Lets the generic sweep lemmas read directly on
the concrete family. -/
theorem stepLoop_withLam {lam lam' C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A)
    (hlam' : 0 ≤ lam') :
    (stepLoop lam C A hlam hA).withLam lam' hlam'
      = stepLoop lam' C A hlam' hA := rfl

/-!
## Closed forms on the stylized loop: both branches in every phase
-/

/-- Below capacity the healthy equilibrium is the offered load itself:
`lfpIcc = λ` whenever `λ < C`. -/
theorem stepLoop_lfpIcc_of_lt {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A)
    (hlt : lam < C) :
    lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam := by
  have hab : (0 : ℝ) ≤ lam * A := mul_nonneg hlam (zero_le_one.trans hA)
  have hmem : lam ∈ Set.Icc (0 : ℝ) (lam * A) :=
    ⟨hlam, le_mul_of_one_le_right hlam hA⟩
  have hfix : (stepLoop lam C A hlam hA).F lam = lam :=
    stepLoop_F_of_lt hlam hA hlt
  refine le_antisymm (lfpIcc_le_of_prefixed hmem hfix.le) ?_
  have hlfp_mem := lfpIcc_mem_Icc hab (stepLoop lam C A hlam hA).F_mapsTo
  calc lam ≤ (stepLoop lam C A hlam hA).F
        (lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A)) :=
      (stepLoop lam C A hlam hA).lam_le_F hlfp_mem.1
    _ = lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) :=
      isFixedPt_lfpIcc hab (stepLoop lam C A hlam hA).F_monotoneOn_Icc
        (stepLoop lam C A hlam hA).F_mapsTo

/-- From the band up, the congested equilibrium sits at full amplification:
`gfpIcc = λ·A` whenever `C ≤ λ·A`. -/
theorem stepLoop_gfpIcc_of_ge {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A)
    (hge : C ≤ lam * A) :
    gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam * A := by
  have hab : (0 : ℝ) ≤ lam * A := mul_nonneg hlam (zero_le_one.trans hA)
  have hpost : lam * A ≤ (stepLoop lam C A hlam hA).F (lam * A) :=
    (stepLoop_F_of_ge hlam hA hge).ge
  refine le_antisymm ?_ (le_gfpIcc_of_postfixed ⟨hab, le_rfl⟩ hpost)
  exact (gfpIcc_mem_Icc hab (stepLoop lam C A hlam hA).F_mapsTo).2

/-- Below the band the congested branch does not exist: even the *greatest*
fixed point is the offered load. -/
theorem stepLoop_gfpIcc_of_healthyOnly {lam C A : ℝ} (hlam : 0 ≤ lam)
    (hA : 1 ≤ A) (h : lam * A < C) :
    gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam := by
  have hab : (0 : ℝ) ≤ lam * A := mul_nonneg hlam (zero_le_one.trans hA)
  have hgfp_mem := gfpIcc_mem_Icc hab (stepLoop lam C A hlam hA).F_mapsTo
  have hfixpt : Function.IsFixedPt (stepLoop lam C A hlam hA).F
      (gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A)) :=
    isFixedPt_gfpIcc hab (stepLoop lam C A hlam hA).F_monotoneOn_Icc
      (stepLoop lam C A hlam hA).F_mapsTo
  have hlt : gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) < C :=
    lt_of_le_of_lt hgfp_mem.2 h
  calc gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A)
      = (stepLoop lam C A hlam hA).F
        (gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A)) := hfixpt.symm
    _ = lam := stepLoop_F_of_lt hlam hA hlt

/-- Past the band's upper edge the healthy branch is gone: even the *least*
fixed point is fully amplified. -/
theorem stepLoop_lfpIcc_of_ge {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A)
    (hover : C ≤ lam) :
    lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam * A := by
  have hab : (0 : ℝ) ≤ lam * A := mul_nonneg hlam (zero_le_one.trans hA)
  have hfixpt : Function.IsFixedPt (stepLoop lam C A hlam hA).F
      (lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A)) :=
    isFixedPt_lfpIcc hab (stepLoop lam C A hlam hA).F_monotoneOn_Icc
      (stepLoop lam C A hlam hA).F_mapsTo
  have hge : C ≤ lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) :=
    hover.trans <| calc
      lam ≤ (stepLoop lam C A hlam hA).F
          (lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A)) :=
        (stepLoop lam C A hlam hA).lam_le_F
          (lfpIcc_mem_Icc hab (stepLoop lam C A hlam hA).F_mapsTo).1
      _ = lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) := hfixpt
  exact hfixpt.symm.trans (stepLoop_F_of_ge hlam hA hge)

/-- **The equilibrium-selection trichotomy.** In each phase region both
extremal equilibria of the stylized loop have closed forms: healthy-only
collapses both to `λ`, the band holds `λ` and `λ·A` apart (the hysteresis
gap), congested-only collapses both to `λ·A`. Which of the band's two
branches a system occupies is exactly the path dependence the jump lemmas
make quantitative. -/
theorem stepLoop_equilibrium_trichotomy {lam C A : ℝ} (hlam : 0 ≤ lam)
    (hA : 1 ≤ A) :
    (HealthyOnly lam A C →
      lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam ∧
      gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam) ∧
    (BistableBand lam A C →
      lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam ∧
      gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam * A) ∧
    (CongestedOnly lam C →
      lfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam * A ∧
      gfpIcc (stepLoop lam C A hlam hA).F 0 (lam * A) = lam * A) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · exact stepLoop_lfpIcc_of_lt hlam hA
      (lt_of_le_of_lt (le_mul_of_one_le_right hlam hA) h)
  · exact stepLoop_gfpIcc_of_healthyOnly hlam hA h
  · exact stepLoop_lfpIcc_of_lt hlam hA h.1
  · exact stepLoop_gfpIcc_of_ge hlam hA h.2
  · exact stepLoop_lfpIcc_of_ge hlam hA h
  · exact stepLoop_gfpIcc_of_ge hlam hA
      (le_trans h (le_mul_of_one_le_right hlam hA))

/-- **The upward jump.** The operative (least) equilibrium tracks the
offered load the whole way to the band's upper edge — and at the crossing
`λ = C` it leaps to full amplification `C·A`: a discontinuity of magnitude
`C·(A−1)` where collapse begins. Strict `1 < A` and `0 < C` are what make
the jump a jump: at `A = 1` the loop has a unique equilibrium
(`noSustaining_unique_eq`) and at `C = 0` both branches sit at zero, so the
first conjunct — the gap `C < C·A` — would be false. -/
theorem stepLoop_jump_up {C A : ℝ} (hC : 0 < C) (hA : 1 < A) :
    C < C * A ∧
    (∀ lam, ∀ hlam : 0 ≤ lam, lam < C →
      lfpIcc (stepLoop lam C A hlam hA.le).F 0 (lam * A) = lam) ∧
    lfpIcc (stepLoop C C A hC.le hA.le).F 0 (C * A) = C * A :=
  ⟨lt_mul_of_one_lt_right hC hA,
    fun _lam _hlam hlt => stepLoop_lfpIcc_of_lt _ hA.le hlt,
    stepLoop_lfpIcc_of_ge hC.le hA.le le_rfl⟩

/-- **The downward jump.** Sweeping load back down, the congested branch
holds all the way to the band's *lower* edge `λ = C/A` — where it still
sustains exactly `C` — and only below it collapses to the offered load.
Collapse began at `C` (`stepLoop_jump_up`); recovery waits for `C/A`. That
the two edges differ is the first conjunct, `C/A < C`, and the drop at the
lower edge then has magnitude `C·(1−1/A) > 0`. Strict `1 < A` and `0 < C`
are what buy the separation: at `A = 1` the two edges coincide and the loop
has a unique equilibrium. This is the hysteresis loop as a pair of certified
endpoints. -/
theorem stepLoop_jump_down {C A : ℝ} (hC : 0 < C) (hA : 1 < A) :
    C / A < C ∧
    gfpIcc (stepLoop (C / A) C A
        (div_nonneg hC.le (zero_le_one.trans hA.le)) hA.le).F 0
        (C / A * A) = C ∧
    ∀ lam, ∀ hlam : 0 ≤ lam, lam * A < C →
      gfpIcc (stepLoop lam C A hlam hA.le).F 0 (lam * A) = lam := by
  have hApos : (0 : ℝ) < A := zero_lt_one.trans hA
  have hA0 : A ≠ 0 := ne_of_gt hApos
  have hcancel : C / A * A = C := div_mul_cancel₀ C hA0
  refine ⟨(div_lt_iff₀ hApos).mpr (lt_mul_of_one_lt_right hC hA), ?_, ?_⟩
  · exact (stepLoop_gfpIcc_of_ge
      (div_nonneg hC.le (zero_le_one.trans hA.le)) hA.le hcancel.ge).trans hcancel
  · exact fun _lam _hlam h => stepLoop_gfpIcc_of_healthyOnly _ hA.le h

/-- Ramp-up safety below the band's upper edge: iterating demand from empty
never overshoots the healthy equilibrium `λ` — the upward sweep stays at or
below the healthy branch until the edge. Sweep *dynamics* (rates, jitter,
trajectories) remain simulator territory; this is the order-theoretic
endpoint any sweep must respect. -/
theorem stepLoop_sweep_up_le {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A)
    (hlt : lam < C) (n : ℕ) :
    (stepLoop lam C A hlam hA).F^[n] 0 ≤ lam := by
  have hab : (0 : ℝ) ≤ lam * A := mul_nonneg hlam (zero_le_one.trans hA)
  have h := iterate_le_lfpIcc hab
    (stepLoop lam C A hlam hA).F_monotoneOn_Icc
    (stepLoop lam C A hlam hA).F_mapsTo n
  rwa [stepLoop_lfpIcc_of_lt hlam hA hlt] at h

/-- Ramp-down inertia from saturation: while the congested equilibrium
exists (`C ≤ λ·A`), iterating demand down from full amplification never
falls below it — the downward sweep is pinned to the congested branch
until the band's lower edge removes it. Mirror of
`stepLoop_sweep_up_le`. -/
theorem stepLoop_sweep_down_ge {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A)
    (hge : C ≤ lam * A) (n : ℕ) :
    lam * A ≤ (stepLoop lam C A hlam hA).F^[n] (lam * A) := by
  have hab : (0 : ℝ) ≤ lam * A := mul_nonneg hlam (zero_le_one.trans hA)
  have h := gfpIcc_le_iterate hab
    (stepLoop lam C A hlam hA).F_monotoneOn_Icc
    (stepLoop lam C A hlam hA).F_mapsTo n
  rwa [stepLoop_gfpIcc_of_ge hlam hA hge] at h

/-- **The congestion edge of the stylized loop is exactly `C/A`.** The
congested set in offered load is precisely `[C/A, ∞)` —
`clamp_band_lower` gives the forward inclusion, the band's congested
equilibrium the reverse — so the infimum evaluates in closed form, and on
this family the edge is attained. Closes the "bounds only" hedge of
`congestionEdge_le`/`le_congestionEdge` on the concrete loop. -/
theorem stepLoop_congestionEdge {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A)
    (hC : 0 < C) :
    (stepLoop lam C A hlam hA).congestionEdge C = C / A := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hCA : 0 < C / A := div_pos hC hA0
  have hedge : {lam' | ∃ h : 0 ≤ lam',
      ((stepLoop lam C A hlam hA).withLam lam' h).CongestedEq C}
      = Set.Ici (C / A) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · rintro ⟨hx0, hcong⟩
      exact clamp_band_lower
        ((stepLoop lam C A hlam hA).withLam x hx0).toBoundedLoop hA0
        (((stepLoop lam C A hlam hA).withLam x hx0).h_le_Amax) hcong
    · intro hx
      have hx0 : 0 ≤ x := hCA.le.trans hx
      refine ⟨hx0, ?_⟩
      rw [stepLoop_withLam hlam hA hx0]
      exact stepLoop_congestedEq (hCA.trans_le hx) hA
        ((div_le_iff₀ hA0).mp hx) hC
  change sInf {lam' | ∃ h : 0 ≤ lam',
      ((stepLoop lam C A hlam hA).withLam lam' h).CongestedEq C} = C / A
  rw [hedge, csInf_Ici]

/-!
## Numeric instances of the selection results

All on one band loop — offered load `2`, capacity `5`, amplification `4`, so
`λ = 2 < 5 ≤ 8 = λ·A` — except the jump lemmas, which quantify over the load
themselves and are pinned at `C = 5`, `A = 4`.
-/

/-- Pin of the trichotomy's band leg: at load `2` under capacity `5` the two
extremal equilibria sit at `2` and `8`, the hysteresis gap in numbers. -/
theorem stepLoop_equilibrium_trichotomy_pin :
    lfpIcc (stepLoop 2 5 4 (by norm_num) (by norm_num)).F 0 (2 * 4) = 2 ∧
      gfpIcc (stepLoop 2 5 4 (by norm_num) (by norm_num)).F 0 (2 * 4) = 2 * 4 :=
  (stepLoop_equilibrium_trichotomy (by norm_num) (by norm_num)).2.1
    (by unfold BistableBand; norm_num)

/-- Pin of the two interval Knaster–Tarski order legs on the same loop: the
least equilibrium sits below the greatest, and `8`, a fixed point of this
loop, sits at or below the greatest as well. -/
theorem operator_bracket_pin :
    lfpIcc (stepLoop 2 5 4 (by norm_num) (by norm_num)).F 0 (2 * 4)
        ≤ gfpIcc (stepLoop 2 5 4 (by norm_num) (by norm_num)).F 0 (2 * 4) ∧
      (2 * 4 : ℝ)
        ≤ gfpIcc (stepLoop 2 5 4 (by norm_num) (by norm_num)).F 0 (2 * 4) :=
  ⟨lfpIcc_le_gfpIcc (by norm_num)
      (stepLoop 2 5 4 (by norm_num) (by norm_num)).F_monotoneOn_Icc
      (stepLoop 2 5 4 (by norm_num) (by norm_num)).F_mapsTo,
    isFixedPt_le_gfpIcc ⟨by norm_num, show (2 : ℝ) * 4 ≤ 2 * 4 by norm_num⟩
      (stepLoop_F_of_ge (by norm_num) (by norm_num) (by norm_num))⟩

/-- Pin of the downward-inertia leg: starting from the congested `8`, three
monotone iterations of the band loop stay at or above the healthy equilibrium
`2`. Monotone iteration alone never crosses a fixed point from above. -/
theorem le_iterate_of_fixedPt_le_pin :
    (2 : ℝ) ≤ (stepLoop 2 5 4 (by norm_num) (by norm_num)).F^[3] (2 * 4) :=
  le_iterate_of_fixedPt_le
    (stepLoop 2 5 4 (by norm_num) (by norm_num)).F_monotoneOn_Icc
    (stepLoop 2 5 4 (by norm_num) (by norm_num)).F_mapsTo
    ⟨by norm_num, show (2 : ℝ) ≤ 2 * 4 by norm_num⟩
    (stepLoop_F_of_lt (by norm_num) (by norm_num) (by norm_num))
    ⟨by norm_num, show (2 : ℝ) * 4 ≤ 2 * 4 by norm_num⟩ (by norm_num) 3

/-- Pin of the upward jump at capacity `5`, amplification `4`: the operative
equilibrium tracks the load below `5` and leaps to `20` at the crossing, a
discontinuity of `15`. -/
theorem stepLoop_jump_up_pin :
    (5 : ℝ) < 5 * 4 ∧
    (∀ lam, ∀ hlam : 0 ≤ lam, lam < 5 →
      lfpIcc (stepLoop lam 5 4 hlam (by norm_num)).F 0 (lam * 4) = lam) ∧
    lfpIcc (stepLoop 5 5 4 (by norm_num) (by norm_num)).F 0 (5 * 4) = 5 * 4 :=
  stepLoop_jump_up (by norm_num) (by norm_num)

/-- Pin of the downward jump at the same numbers: the congested branch holds
down to `5/4`, where it still sustains `5`, and collapse to the offered load
waits until below it. Recovery at `5/4` against collapse at `5` is the
hysteresis width. -/
theorem stepLoop_jump_down_pin :
    (5 : ℝ) / 4 < 5 ∧
    gfpIcc (stepLoop (5 / 4) 5 4 (by norm_num) (by norm_num)).F 0
        (5 / 4 * 4) = 5 ∧
    ∀ lam, ∀ hlam : 0 ≤ lam, lam * 4 < 5 →
      gfpIcc (stepLoop lam 5 4 hlam (by norm_num)).F 0 (lam * 4) = lam :=
  stepLoop_jump_down (by norm_num) (by norm_num)

/-- Pin of both sweep legs on the band loop at three iterations: from empty,
demand stays at or below the healthy `2`; from full amplification, it stays at
or above the congested `8`. Same operator, same iteration count, two
branches. -/
theorem stepLoop_sweep_pin :
    (stepLoop 2 5 4 (by norm_num) (by norm_num)).F^[3] 0 ≤ 2 ∧
      (2 : ℝ) * 4 ≤ (stepLoop 2 5 4 (by norm_num) (by norm_num)).F^[3] (2 * 4) :=
  ⟨stepLoop_sweep_up_le (by norm_num) (by norm_num) (by norm_num) 3,
    stepLoop_sweep_down_ge (by norm_num) (by norm_num) (by norm_num) 3⟩

/-- Pin of the closed-form edge and of the two generic bounds it closes: the
band loop's congestion edge at threshold `5` is exactly `5/4`, the generic
lower bound `Θ/Amax` is attained there, and loading the mechanism to `5`
bounds the edge from above. -/
theorem stepLoop_congestionEdge_pin :
    (stepLoop 2 5 4 (by norm_num) (by norm_num)).congestionEdge 5 = 5 / 4 ∧
      (5 : ℝ) / 4 ≤ (stepLoop 2 5 4 (by norm_num) (by norm_num)).congestionEdge 5 ∧
      (stepLoop 2 5 4 (by norm_num) (by norm_num)).congestionEdge 5 ≤ 5 := by
  refine ⟨stepLoop_congestionEdge (by norm_num) (by norm_num) (by norm_num),
    (stepLoop 2 5 4 (by norm_num) (by norm_num)).le_congestionEdge,
    (stepLoop 2 5 4 (by norm_num) (by norm_num)).congestionEdge_le
      (by norm_num) ?_⟩
  exact ((stepLoop 2 5 4 (by norm_num) (by norm_num)).withLam 5
    (by norm_num)).congestedEq_of_over le_rfl

end Overload
