module

public import Overload.Basic -- shake: keep
public import Overload.Loop.Operator
public import Overload.Retry.Amplification
public import Overload.Retry.Deadline
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

/-!
# Closed-loop demand: congested equilibria, the clamp theorem, and the
sustaining-mechanisms audit

The Level-1 model: the environment responds to load through a
failure kernel `g` (attempt rate → per-attempt failure probability), and
demand responds to failure through an amplification response `h` (failure
probability → expected attempts per request). Steady state is a fixed point
of `F(Λ) = λ·h(g(Λ))`.

The model splits in two. `BoundedLoop` is the boundedness core (kernel in
`[0,1]`, response under `Amax` — nothing else); the safety certificates live
there, so batching kernels and backpressure clients inherit them without
being monotone or amplifying. `ClosedLoop` extends it with monotonicity and
the `1 ≤ h` floor; everything order-theoretic lives there.

Headline results:

* `BoundedLoop.clamp_no_congestedEq` — **the clamp theorem**: an
  amplification clamp `h ≤ K` with `λ·K < Θ` removes every congested
  equilibrium. *No timing, backoff, latency, kernel-shape, or monotonicity
  hypotheses.* Budget (`K = 1+β`) and attempt-cap (`K = n`) corollaries.
* `congestedEq_of_inflow` — the one-inequality **inflow certificate**:
  `Θ ≤ F(Θ)` (attempt inflow at the threshold exceeds it) produces a genuine
  congested equilibrium by Knaster–Tarski.
* `noSustaining_no_congestedEq` — **the sustaining-mechanisms audit**: if the
  amplification response is trivial (`h ≡ 1` — discharged for slow failures
  under remaining-deadline apportionment by `Deadline.neff_slow_remaining`),
  the loop has spill-free structure (built into `F = λ·h∘g`), and the
  threshold is undegraded capacity, then `λ < C` leaves *no* congested
  equilibrium: overload without a sustaining mechanism is transient, not
  metastable. Contrapositive: a bistable loop exhibits fast-fail
  amplification, re-armed timeouts, spill-in coupling, or supply degradation.
* `bistableOn_of_two_points` / `two_fixedPts_of_two_points` — the loop-level
  two-point band certificate: memberships derive from the loop's own envelope
  (`F_le`), so an instance supplies only its two point evaluations of `F`.
* `stepLoop_bistable` / `stepLoop_congestedEq` / `stepLoop_two_fixedPts` —
  the bistable band `[C/A, C)` on the stylized saturated kernel, with the
  order gap upgraded to two genuine equilibria, and `clamp_band_lower`: any
  clamp `h ≤ K` pushes the band's lower edge up to `C/K`. On the stylized
  loop that edge is exact (`stepLoop_congestedEq_iff`), which prices added
  offered load at `C/A - lam` (`stepLoop_injectable_load`).
* `blip_unique_eq` — retrying a load-*independent* failure channel buys
  masking without bistability: the equilibrium is unique.
-/

@[expose] public section

namespace Overload

/-- The boundedness core of a closed-loop demand model: offered rate `lam`,
failure kernel `g` landing in `[0, 1]`, amplification response `h` bounded
by `Amax`. Deliberately **no monotonicity and no amplifying-client floor**:
the safety certificates (`clamp_no_congestedEq` and its corollaries) consume
only this much, so systems outside the monotone class — batching kernels
(failure *falls* as load batches), backpressure clients (`h < 1`) — can
instantiate the base and inherit them. Everything order-theoretic
(equilibrium existence, bands, basins) needs the monotone extension
`ClosedLoop`. -/
structure BoundedLoop where
  /-- Offered fresh-request rate. -/
  lam : ℝ
  /-- The load-coupled failure kernel: attempt rate → per-attempt failure
  probability. -/
  g : ℝ → ℝ
  /-- The amplification response: failure probability → expected attempts per
  request. -/
  h : ℝ → ℝ
  /-- Upper bound on the amplification response. -/
  Amax : ℝ
  /-- The offered fresh-request rate is nonnegative. -/
  lam_nonneg : 0 ≤ lam
  /-- The failure kernel lands in `[0, 1]` at every nonnegative attempt
  rate. -/
  g_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1
  /-- The amplification response never exceeds `Amax` on `[0, 1]`. -/
  h_le_Amax : ∀ p ∈ Set.Icc (0 : ℝ) 1, h p ≤ Amax

/-- A closed-loop demand model over a shared bottleneck: the boundedness
core plus a monotone kernel, a monotone response, and the amplifying-client
floor `1 ≤ h`. Demand balance is `Λ = lam · h (g Λ)`. -/
structure ClosedLoop extends BoundedLoop where
  /-- The failure kernel is monotone on nonnegative attempt rates. -/
  g_mono : MonotoneOn g (Set.Ici (0 : ℝ))
  /-- The amplification response is monotone on `[0, 1]`. -/
  h_mono : MonotoneOn h (Set.Icc (0 : ℝ) 1)
  /-- The amplifying-client floor: `1 ≤ h` on `[0, 1]`. -/
  h_one_le : ∀ p ∈ Set.Icc (0 : ℝ) 1, 1 ≤ h p

namespace BoundedLoop

variable (L : BoundedLoop)

/-- The demand operator `F(Λ) = λ·h(g(Λ))`. -/
def F (Λ : ℝ) : ℝ := L.lam * L.h (L.g Λ)

/-- The demand envelope: `F` never exceeds `λ·Amax`. Boundedness alone. -/
theorem F_le {x : ℝ} (hx : 0 ≤ x) : L.F x ≤ L.lam * L.Amax :=
  mul_le_mul_of_nonneg_left (L.h_le_Amax _ (L.g_mem x hx)) L.lam_nonneg

/-- A congested equilibrium at threshold `Θ`: a self-sustaining demand level
at or above `Θ`. Take `Θ = C` normally, or `Θ = C_cong < C` under
congestion-induced supply degradation.

Deliberately left unguarded at `Θ ≤ 0`, where the predicate is degenerate on
the closed-loop side: *every* `ClosedLoop` satisfies it there, because
`Θ ≤ 0 ≤ lam` puts the loop in the congested-only region
(`ClosedLoop.congestedEq_of_nonpos_threshold`, `Universality.lean`). That
route is Knaster–Tarski and needs monotonicity, so it does not extend to a
bare `BoundedLoop`, whose `F` may have no fixed point at all and then fail
`CongestedEq` at every `Θ`. Read closed-loop congestion statements at a
positive threshold. -/
def CongestedEq (Θ : ℝ) : Prop := ∃ Λ, 0 ≤ Λ ∧ L.F Λ = Λ ∧ Θ ≤ Λ

/-- **The clamp theorem.** An amplification clamp `h ≤ K` with `λ·K < Θ`
removes every congested equilibrium — with *zero* timing, backoff, latency,
kernel-shape, or even monotonicity hypotheses (it lives on the boundedness
core). Mechanisms that enforce such a clamp — budgets, attempt caps, the
open-state breaker (`Breaker.lean`) — destroy the congested equilibrium
rather than resisting entry to it. -/
theorem clamp_no_congestedEq {K Θ : ℝ}
    (hclamp : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p ≤ K) (hK : L.lam * K < Θ) :
    ¬L.CongestedEq Θ := by
  rintro ⟨Λ, hΛ0, hfix, hΘΛ⟩
  have hg := L.g_mem Λ hΛ0
  have hle : Λ ≤ L.lam * K := by
    rw [← hfix]
    exact mul_le_mul_of_nonneg_left (hclamp _ hg) L.lam_nonneg
  linarith

/-- **Budget corollary**: an aggregate retry budget `β` (at most `1 + β`
attempts per request on average) with `λ(1+β) < Θ` removes the congested
equilibrium. -/
theorem budget_no_congestedEq {β Θ : ℝ}
    (hbudget : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p ≤ 1 + β)
    (hK : L.lam * (1 + β) < Θ) : ¬L.CongestedEq Θ :=
  L.clamp_no_congestedEq hbudget hK

/-- **Attempt-cap corollary**: a truncated-geometric response capped at `n`
attempts with `λ·n < Θ` removes the congested equilibrium
(`expAttempts_le_cap` supplies the clamp). -/
theorem cap_no_congestedEq {n : ℕ} {Θ : ℝ}
    (hh : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p = expAttempts p n)
    (hK : L.lam * n < Θ) : ¬L.CongestedEq Θ := by
  refine L.clamp_no_congestedEq (fun p hp => ?_) hK
  rw [hh p hp]
  exact expAttempts_le_cap hp.1 hp.2 n

end BoundedLoop

namespace ClosedLoop

variable (L : ClosedLoop)

/-- The bound on the amplification response is at least one:
`1 ≤ h(0) ≤ Amax`, the floor `1 ≤ h` chained with `h_le_Amax` at `p = 0`. -/
theorem one_le_Amax : 1 ≤ L.Amax :=
  le_trans (L.h_one_le 0 ⟨le_rfl, zero_le_one⟩)
    (L.h_le_Amax 0 ⟨le_rfl, zero_le_one⟩)

/-- `F` is nonnegative on nonnegative demand: `0 ≤ λ` and `1 ≤ h`. -/
theorem F_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ L.F x :=
  mul_nonneg L.lam_nonneg
    (le_trans zero_le_one (L.h_one_le _ (L.g_mem x hx)))

/-- The offered load is a lower bound on `F` on nonnegative demand: the
floor `1 ≤ h` scaled by `λ ≥ 0`. -/
theorem lam_le_F {x : ℝ} (hx : 0 ≤ x) : L.lam ≤ L.F x :=
  le_mul_of_one_le_right L.lam_nonneg (L.h_one_le _ (L.g_mem x hx))

/-- `F` is monotone on `[0, ∞)`: the monotone kernel composed with the
monotone response, scaled by `λ ≥ 0`. -/
theorem F_monotoneOn : MonotoneOn L.F (Set.Ici (0 : ℝ)) :=
  fun x hx y hy hxy =>
    mul_le_mul_of_nonneg_left
      (L.h_mono (L.g_mem x hx) (L.g_mem y hy) (L.g_mono hx hy hxy))
      L.lam_nonneg

/-- `F_monotoneOn` restricted to the envelope `[0, λ·Amax]`. -/
theorem F_monotoneOn_Icc : MonotoneOn L.F (Set.Icc 0 (L.lam * L.Amax)) :=
  L.F_monotoneOn.mono fun _x hx => hx.1

/-- `F` maps the envelope `[0, λ·Amax]` into itself: `F_nonneg` below,
`F_le` above. -/
theorem F_mapsTo :
    Set.MapsTo L.F (Set.Icc 0 (L.lam * L.Amax))
      (Set.Icc 0 (L.lam * L.Amax)) :=
  fun _x hx => ⟨L.F_nonneg hx.1, L.F_le hx.1⟩

/-- **The two-point band certificate, at loop level.** One demand level
pushed down (`F x ≤ x`), a strictly larger one pushed up (`y ≤ F y`), and
any ceiling `b` at or above the demand envelope `λ·Amax`: the loop is
bistable on `[0, b]`. The memberships of `bistableOn_of_certificate` are
derived once here — `0 ≤ y` from `x < y`, both upper bounds from `F_le`
through `hb` — so an instance checks two point evaluations of `F` and one
envelope inequality. -/
theorem bistableOn_of_two_points {x y b : ℝ} (hx0 : 0 ≤ x)
    (hFx : L.F x ≤ x) (hyF : y ≤ L.F y) (hxy : x < y)
    (hb : L.lam * L.Amax ≤ b) : BistableOn L.F 0 b := by
  have hy0 : 0 ≤ y := (lt_of_le_of_lt hx0 hxy).le
  have hyb : y ≤ b := hyF.trans ((L.F_le hy0).trans hb)
  exact bistableOn_of_certificate ⟨hx0, hxy.le.trans hyb⟩ hFx ⟨hy0, hyb⟩
    hyF hxy

/-- The two-point certificate upgraded to two genuine, separated equilibria
of the loop — memberships derived as in `bistableOn_of_two_points`,
monotonicity and invariance supplied by the loop itself. -/
theorem two_fixedPts_of_two_points {x y : ℝ} (hx0 : 0 ≤ x)
    (hFx : L.F x ≤ x) (hyF : y ≤ L.F y) (hxy : x < y) :
    ∃ z₁ z₂, Function.IsFixedPt L.F z₁ ∧ Function.IsFixedPt L.F z₂ ∧
      z₁ ≤ x ∧ y ≤ z₂ ∧ z₁ < z₂ := by
  have hy0 : 0 ≤ y := (lt_of_le_of_lt hx0 hxy).le
  have hyb : y ≤ L.lam * L.Amax := hyF.trans (L.F_le hy0)
  exact exists_two_fixedPts_of_certificate L.F_monotoneOn_Icc L.F_mapsTo
    ⟨hx0, hxy.le.trans hyb⟩ hFx ⟨hy0, hyb⟩ hyF hxy

/-- **The inflow certificate**: if attempt inflow at the threshold already
meets the threshold (`Θ ≤ F Θ`), a genuine congested equilibrium exists (by
Knaster–Tarski above `Θ`). One inequality to check. -/
theorem congestedEq_of_inflow {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ : Θ ≤ L.F Θ) :
    L.CongestedEq Θ := by
  have hΘM : Θ ≤ L.lam * L.Amax := le_trans hΘ (L.F_le hΘ0)
  obtain ⟨z, hzmem, hzfix⟩ := exists_fixedPt_ge (F := L.F)
    (a := 0) (b := L.lam * L.Amax) L.F_monotoneOn_Icc L.F_mapsTo
    ⟨hΘ0, hΘM⟩ hΘ
  exact ⟨z, le_trans hΘ0 hzmem.1, hzfix, hzmem.1⟩

/-!
## The sustaining-mechanisms audit
-/

/-- The formal residue of "none of the four sustaining mechanisms is
present": the amplification response is trivial. Discharged concretely by
`amp_eq_one_of_slow_remaining` below — slow failures under remaining-deadline
apportionment admit one attempt (`neff_slow_remaining`), and one attempt
means no amplification (Mathlib's `geom_sum_one`). The other two mechanisms are
structural here: `F = λ·h∘g` has no additive spill-in term, and taking the
threshold to be the *undegraded* capacity `C` asserts no supply degradation. -/
def NoSustaining (L : ClosedLoop) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p = 1

/-- With no sustaining mechanism, the loop is load-transparent: `F ≡ λ`. -/
theorem F_eq_lam_of_noSustaining (hns : L.NoSustaining) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) : L.F Λ = L.lam := by
  unfold BoundedLoop.F
  rw [hns _ (L.g_mem Λ hΛ), mul_one]

variable {L} in
/-- With no sustaining mechanism the equilibrium is unique — it is the
offered load itself. -/
theorem noSustaining_unique_eq (hns : L.NoSustaining) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    L.F Λ = Λ ↔ Λ = L.lam := by
  rw [L.F_eq_lam_of_noSustaining hns hΛ]
  exact eq_comm

/-- **The sustaining-mechanisms theorem**: absent all four mechanisms, any
offered load below capacity leaves no congested equilibrium — overload
without a sustaining mechanism is transient, not metastable. Contrapositive:
a bistable system exhibits at least one auditable mechanism (fast-fail
amplification, re-armed timeouts, spill-in coupling, or supply degradation). -/
theorem noSustaining_no_congestedEq (hns : L.NoSustaining) {C : ℝ}
    (hlt : L.lam < C) : ¬L.CongestedEq C := by
  rintro ⟨Λ, hΛ0, hfix, hCΛ⟩
  rw [(noSustaining_unique_eq hns hΛ0).mp hfix] at hCΛ
  linarith

variable {L} in
/-- Retrying a load-*independent* failure channel ("blips") buys masking
without bistability: the equilibrium is unique. Only channels that are both
retry-eligible and load-coupled destabilize. -/
theorem blip_unique_eq {p₀ : ℝ} (hg : ∀ x, 0 ≤ x → L.g x = p₀) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) : L.F Λ = Λ ↔ Λ = L.lam * L.h p₀ := by
  unfold BoundedLoop.F
  rw [hg Λ hΛ]
  exact eq_comm

/-- **A load-blind kernel is monostable.** With `g` constant the demand
operator is constant, so both extremal equilibria of the loop's own envelope
`[0, lam·Amax]` collapse onto the single value `lam·h p₀`: the loop is not
bistable. This is the order-gap half of `blip_unique_eq`, and it discharges
the asymmetry `Universality.lean` states in prose — a band position makes
bistability *possible*, not automatic, and a load-independent failure channel
never realizes it. -/
theorem not_bistableOn_of_const {p₀ : ℝ} (hg : ∀ x, 0 ≤ x → L.g x = p₀) :
    ¬BistableOn L.F 0 (L.lam * L.Amax) := by
  have hab : (0 : ℝ) ≤ L.lam * L.Amax :=
    mul_nonneg L.lam_nonneg (le_trans zero_le_one L.one_le_Amax)
  have hlmem := lfpIcc_mem_Icc hab L.F_mapsTo
  have hgmem := gfpIcc_mem_Icc hab L.F_mapsTo
  have hlfix : L.F (lfpIcc L.F 0 (L.lam * L.Amax))
      = lfpIcc L.F 0 (L.lam * L.Amax) :=
    isFixedPt_lfpIcc hab L.F_monotoneOn_Icc L.F_mapsTo
  have hgfix : L.F (gfpIcc L.F 0 (L.lam * L.Amax))
      = gfpIcc L.F 0 (L.lam * L.Amax) :=
    isFixedPt_gfpIcc hab L.F_monotoneOn_Icc L.F_mapsTo
  have hl := (blip_unique_eq hg hlmem.1).mp hlfix
  have hg' := (blip_unique_eq hg hgmem.1).mp hgfix
  change ¬lfpIcc L.F 0 (L.lam * L.Amax) < gfpIcc L.F 0 (L.lam * L.Amax)
  rw [hl, hg']
  exact lt_irrefl _

end ClosedLoop

/-!
## The sustaining-mechanisms discharge from deadline arithmetic

Connecting `Deadline` to `ClosedLoop`: an amplification response built from
the deadline-capped attempt count collapses to `NoSustaining` exactly when
failures are slow and apportionment is remaining-deadline; re-armed per-try
timeouts re-open it.
-/

/-- Slow failure + remaining-deadline apportionment ⟹ the truncated-geometric
response through the deadline-capped attempt count is identically 1: no
amplification, whatever the failure probability. -/
theorem amp_eq_one_of_slow_remaining {T B : ℕ → ℝ} {D : ℝ} {n : ℕ}
    (hT0 : T 0 = D) (hTpos : ∀ j, 0 < T j) (hB : ∀ j, 0 ≤ B j)
    (hn : 1 ≤ n) (p : ℝ) : expAttempts p (neff T B D n) = 1 := by
  rw [neff_slow_remaining hT0 hTpos hB hn, expAttempts_def]
  exact geom_sum_one p

/-- Re-armed per-try timeouts re-open amplification: with two sub-deadlines
in the budget, the response is at least `1 + p` — strictly amplifying on any
load-coupled channel. -/
theorem one_add_le_amp_of_rearmed {τ D : ℝ} {n : ℕ} (hτ : 0 < τ)
    (h2 : 2 * τ ≤ D) (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    1 + p ≤ expAttempts p (neff (fun _ => τ) (fun _ => 0) D n) :=
  one_add_le_expAttempts hp (two_le_neff_rearmed hτ h2 hn)

/-- Pin of the slow-remaining collapse at `T ≡ 1 = D`, cap 3: the deadline
admits one attempt and the response is exactly one at `p = 1/2`. -/
theorem amp_eq_one_of_slow_remaining_pin :
    expAttempts (1 / 2) (neff (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) 1 3) = 1 :=
  amp_eq_one_of_slow_remaining rfl (fun _ => one_pos) (fun _ => le_rfl)
    (by norm_num) (1 / 2)

/-- Pin of the re-armed re-opening at `τ = 1, D = 2, n = 2, p = 1/2`: two
sub-deadlines fit and the response is at least `3/2` — attained exactly
(`expAttempts (1/2) 2 = 3/2`), so the bound is sharp here. -/
theorem one_add_le_amp_of_rearmed_pin :
    (1 : ℝ) + 1 / 2
      ≤ expAttempts (1 / 2) (neff (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) 2 2) :=
  one_add_le_amp_of_rearmed one_pos (by norm_num) le_rfl (by norm_num)

/-!
## The bistable band on the stylized saturated kernel
-/

open Classical in
/-- The saturated step kernel: failures are absent below capacity `C` and
saturated at and above it. The shared load coupling of the stylized loops
(the boundary value at `Λ = C` is a modeling choice — it is what closes the
band's lower edge in `stepLoop_congestedEq` and `bistableBand_iff_edges`). -/
noncomputable def stepKernel (C : ℝ) : ℝ → ℝ := fun Λ => if Λ < C then 0 else 1

/-- Below capacity the step kernel vanishes. -/
theorem stepKernel_of_lt {C Λ : ℝ} (h : Λ < C) : stepKernel C Λ = 0 :=
  if_pos h

/-- At and above capacity the step kernel saturates. -/
theorem stepKernel_of_ge {C Λ : ℝ} (h : C ≤ Λ) : stepKernel C Λ = 1 :=
  if_neg (not_lt.mpr h)

/-- The step kernel lands in `[0, 1]`. Supplies `g_mem` for `stepLoop` and
`cappedLoop`. -/
theorem stepKernel_mem (C : ℝ) :
    ∀ x, 0 ≤ x → stepKernel C x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x _
  unfold stepKernel
  split <;> constructor <;> norm_num

/-- The step kernel is monotone on `[0, ∞)`. Supplies `g_mono` for
`stepLoop` and `cappedLoop`. -/
theorem stepKernel_monoOn (C : ℝ) :
    MonotoneOn (stepKernel C) (Set.Ici (0 : ℝ)) := by
  intro x _hx y _hy hxy
  by_cases hyC : y < C
  · rw [stepKernel_of_lt (lt_of_le_of_lt hxy hyC), stepKernel_of_lt hyC]
  · by_cases hxC : x < C
    · rw [stepKernel_of_lt hxC, stepKernel_of_ge (not_lt.mp hyC)]
      norm_num
    · rw [stepKernel_of_ge (not_lt.mp hxC), stepKernel_of_ge (not_lt.mp hyC)]

/-- The stylized saturated loop: failures follow the step kernel and the
amplification response interpolates from `1` (no failures) to `A`
(saturated). The minimal model exhibiting the band. -/
noncomputable def stepLoop (lam C A : ℝ) (hlam : 0 ≤ lam) (hA : 1 ≤ A) :
    ClosedLoop where
  lam := lam
  g := stepKernel C
  h := fun p => 1 + p * (A - 1)
  Amax := A
  lam_nonneg := hlam
  g_mem := stepKernel_mem C
  g_mono := stepKernel_monoOn C
  h_mono := by
    intro p _hp q _hq hpq
    dsimp only
    have := mul_le_mul_of_nonneg_right hpq (sub_nonneg.mpr hA)
    linarith
  h_one_le := by
    intro p hp
    have := mul_nonneg hp.1 (sub_nonneg.mpr hA)
    linarith
  h_le_Amax := by
    intro p hp
    have := mul_le_of_le_one_left (sub_nonneg.mpr hA) hp.2
    linarith

/-- The generic truncated-geometric loop over an arbitrary kernel: retries
capped at `m` attempts against a load-coupled failure kernel `g`. The
kernel is where a concrete system's load coupling enters — the saturated
step (`cappedLoop`), the M/M/1 sojourn tail (`MM1.mm1Loop`), or anything
else satisfying the two kernel hypotheses. -/
noncomputable def kernelLoop (lam : ℝ) (g : ℝ → ℝ) (m : ℕ) (hlam : 0 ≤ lam)
    (hm : 1 ≤ m) (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))) : ClosedLoop where
  lam := lam
  g := g
  h := fun p => expAttempts p m
  Amax := m
  lam_nonneg := hlam
  g_mem := hg_mem
  g_mono := hg_mono
  h_mono := fun _p hp _q _ hpq => expAttempts_mono_left hp.1 hpq m
  h_one_le := fun _p hp => one_le_expAttempts hp.1 hm
  h_le_Amax := fun _p hp => expAttempts_le_cap hp.1 hp.2 m

/-- The truncated-geometric loop over the step kernel: the amplification
response is `expAttempts · m` for an attempt cap `m` (a redrive policy, a
restart limit), saturating at `Amax = m`. -/
noncomputable def cappedLoop (lam C : ℝ) (m : ℕ) (hlam : 0 ≤ lam)
    (hm : 1 ≤ m) : ClosedLoop :=
  kernelLoop lam (stepKernel C) m hlam hm (stepKernel_mem C)
    (stepKernel_monoOn C)

/-- Below capacity the truncated-geometric loop is load-transparent: the
step kernel vanishes and a lone attempt is the whole response. -/
theorem cappedLoop_F_of_lt {lam C : ℝ} {m : ℕ} {hlam : 0 ≤ lam} {hm : 1 ≤ m}
    {Λ : ℝ} (hΛ : Λ < C) : (cappedLoop lam C m hlam hm).F Λ = lam := by
  change lam * expAttempts (stepKernel C Λ) m = lam
  rw [stepKernel_of_lt hΛ, expAttempts_at_zero hm, mul_one]

/-- At and above capacity the truncated-geometric loop is fully amplified:
the kernel saturates and the whole cap is spent. -/
theorem cappedLoop_F_of_ge {lam C : ℝ} {m : ℕ} {hlam : 0 ≤ lam} {hm : 1 ≤ m}
    {Λ : ℝ} (hΛ : C ≤ Λ) : (cappedLoop lam C m hlam hm).F Λ = lam * m := by
  change lam * expAttempts (stepKernel C Λ) m = lam * m
  rw [stepKernel_of_ge hΛ, expAttempts_def, one_geom_sum]

/-- The attempt-cap corollary, discharged for the truncated-geometric
constructor: `λ·m < Θ` alone removes every congested equilibrium of a
`cappedLoop` (its response *is* `expAttempts · m`, so the kernel identity
is `rfl`). -/
theorem cappedLoop_no_congestedEq {lam C : ℝ} {m : ℕ} {Θ : ℝ}
    {hlam : 0 ≤ lam} {hm : 1 ≤ m} (hK : lam * m < Θ) :
    ¬(cappedLoop lam C m hlam hm).CongestedEq Θ :=
  (cappedLoop lam C m hlam hm).cap_no_congestedEq (fun _p _hp => rfl) hK

/-- Below capacity the stylized loop is load-transparent: `F(Λ) = λ`. -/
theorem stepLoop_F_of_lt {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A) {Λ : ℝ}
    (hΛ : Λ < C) : (stepLoop lam C A hlam hA).F Λ = lam := by
  change lam * (1 + stepKernel C Λ * (A - 1)) = lam
  rw [stepKernel_of_lt hΛ]
  ring

/-- At or above capacity the stylized loop is fully amplified:
`F(Λ) = λ·A`. -/
theorem stepLoop_F_of_ge {lam C A : ℝ} (hlam : 0 ≤ lam) (hA : 1 ≤ A) {Λ : ℝ}
    (hΛ : C ≤ Λ) : (stepLoop lam C A hlam hA).F Λ = lam * A := by
  change lam * (1 + stepKernel C Λ * (A - 1)) = lam * A
  rw [stepKernel_of_ge hΛ]
  ring

/-- **The bistable band, existence side**: for `λ < C ≤ λ·A` the stylized
loop is bistable — the healthy equilibrium `λ` and a congested equilibrium
`≥ C` coexist, certified by two point evaluations. -/
theorem stepLoop_bistable {lam C A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hband_lo : C ≤ lam * A) (hband_hi : lam < C) :
    BistableOn (stepLoop lam C A (le_of_lt hlam) hA).F 0 (lam * A) :=
  (stepLoop lam C A (le_of_lt hlam) hA).bistableOn_of_two_points
    (le_of_lt hlam)
    (le_of_eq (stepLoop_F_of_lt (le_of_lt hlam) hA hband_hi))
    (hband_lo.trans_eq (stepLoop_F_of_ge (le_of_lt hlam) hA le_rfl).symm)
    hband_hi le_rfl

/-- The congested equilibrium of the band is genuine (a fixed point at or
above `C`), via the inflow certificate. -/
theorem stepLoop_congestedEq {lam C A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hband_lo : C ≤ lam * A) (hC : 0 < C) :
    (stepLoop lam C A (le_of_lt hlam) hA).CongestedEq C := by
  refine (stepLoop lam C A (le_of_lt hlam) hA).congestedEq_of_inflow
    (le_of_lt hC) ?_
  rw [stepLoop_F_of_ge (le_of_lt hlam) hA le_rfl]
  exact hband_lo

/-- **The band's equilibria are genuine.** Inside the band the stylized loop
has two distinct fixed points: a healthy one at or below `λ` and a congested
one at or above `C`. This upgrades the `BistableOn` order gap — which by
itself asserts nothing about fixed points — to actual coexisting equilibria,
using the loop's monotonicity. -/
theorem stepLoop_two_fixedPts {lam C A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hband_lo : C ≤ lam * A) (hband_hi : lam < C) :
    ∃ z₁ z₂,
      Function.IsFixedPt (stepLoop lam C A (le_of_lt hlam) hA).F z₁ ∧
      Function.IsFixedPt (stepLoop lam C A (le_of_lt hlam) hA).F z₂ ∧
      z₁ ≤ lam ∧ C ≤ z₂ ∧ z₁ < z₂ :=
  (stepLoop lam C A (le_of_lt hlam) hA).two_fixedPts_of_two_points
    (le_of_lt hlam)
    (le_of_eq (stepLoop_F_of_lt (le_of_lt hlam) hA hband_hi))
    (hband_lo.trans_eq (stepLoop_F_of_ge (le_of_lt hlam) hA le_rfl).symm)
    hband_hi

/-- **Any clamp narrows the band**: under `h ≤ K`, a congested equilibrium at
threshold `C` forces `λ ≥ C/K`. The band's lower edge is `C/K`; at `K = 1+β`
with small `β` the band is a sliver. Stated on the boundedness core: the
proof is the clamp theorem contraposed, so batching kernels and backpressure
clients get the band's lower edge without being monotone. -/
theorem clamp_band_lower (L : BoundedLoop) {K C : ℝ} (hK : 0 < K)
    (hclamp : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p ≤ K)
    (hcong : L.CongestedEq C) : C / K ≤ L.lam := by
  by_contra h
  exact absurd hcong
    (L.clamp_no_congestedEq hclamp ((lt_div_iff₀ hK).mp (not_le.mp h)))

/-- **The band's lower edge is exact on the stylized loop.** The bound
`clamp_band_lower` gives at `K = A` is attained here: the stylized loop has a
congested equilibrium at capacity if and only if `C / A ≤ lam`. Forward, the
clamp is the loop's own response bound `h_le_Amax`; backward, the inequality
rearranges to `C ≤ lam * A` and `stepLoop_congestedEq` supplies the
equilibrium. The equivalence is specific to `stepLoop`. `clamp_band_lower`
stays one-directional in general, because a response bounded by `K` need not
attain `K`. -/
theorem stepLoop_congestedEq_iff {lam C A : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hC : 0 < C) :
    (stepLoop lam C A hlam.le hA).CongestedEq C ↔ C / A ≤ lam := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  constructor
  · intro hcong
    exact clamp_band_lower (stepLoop lam C A hlam.le hA).toBoundedLoop hA0
      (stepLoop lam C A hlam.le hA).h_le_Amax hcong
  · intro h
    exact stepLoop_congestedEq hlam hA ((div_le_iff₀ hA0).mp h) hC

/-- **Added offered load reaches the congested band exactly at `C / A - lam`.**
Adding `δ` to a baseline offered load `lam` gives the stylized loop a
congested equilibrium at capacity if and only if `C / A - lam ≤ δ`. The
figure is exact rather than sufficient: by the equivalence, no smaller
addition produces such an equilibrium.

What this does not prove: that load of that size is available or
deliverable; that the congested equilibrium is *reached* from a given
starting demand (the crossing arithmetic is `Burst.lean`); and nothing about
the failure kernel, which the added load leaves untouched. -/
theorem stepLoop_injectable_load {lam C A δ : ℝ} (hlam : 0 < lam) (hA : 1 ≤ A)
    (hC : 0 < C) (hδ0 : 0 ≤ δ) :
    (stepLoop (lam + δ) C A (by positivity) hA).CongestedEq C ↔
      C / A - lam ≤ δ := by
  have key := stepLoop_congestedEq_iff (lam := lam + δ) (C := C) (A := A)
    (by linarith) hA hC
  constructor
  · intro hcong
    have := key.mp hcong
    linarith
  · intro h
    exact key.mpr (by linarith)

/-- Pin of the exact injectable-load figure at `lam = 1, C = 10, A = 5`
(threshold `C/A − lam = 1`): `δ = 1` yields the congested equilibrium and
`δ = 1/2` does not — exact on both sides. -/
theorem stepLoop_injectable_load_pin :
    (stepLoop (1 + 1) 10 5 (by positivity) (by norm_num)).CongestedEq 10 ∧
      ¬(stepLoop (1 + 1 / 2) 10 5 (by positivity)
          (by norm_num)).CongestedEq 10 :=
  ⟨(stepLoop_injectable_load (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).mpr (by norm_num),
   fun h => by
     have := (stepLoop_injectable_load (lam := 1) (C := 10) (A := 5)
       (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
       (by norm_num)).mp h
     norm_num at this⟩

end Overload
