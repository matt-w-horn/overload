module

public import Overload.Basic -- shake: keep
public import Overload.Queueing.MM1
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
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
# Calculus: stability by slope, and recovery times by integration

The order-theoretic results read the loop through inequalities on `F`
itself; this module reads the same loop through derivatives:

* **Amplification sensitivity** `expAttemptsDeriv p n`, the derivative of
  the truncated-geometric response `expAttempts · n` at `p`. At `0 ≤ p` it
  is at least `1` whenever a second attempt exists
  (`one_le_expAttemptsDeriv`), so on that range the flag `h'(p) > 0` is
  raised by every retry response with `2 ≤ n` (`expAttemptsDeriv_pos`).
* **Loop gain** `deriv F Λ`, computed by the chain rule as `λ·h'(g Λ)·g'(Λ)`
  (`BoundedLoop.hasDerivAt_F`). Gain above `1` around an equilibrium makes
  the equilibrium repelling (`gain_gt_one_repels`); gain below `1` across
  the demand envelope leaves at most one equilibrium
  (`fixedPt_unique_of_gain_lt_one`) and excludes the bistable band outright
  (`ClosedLoop.not_bistableOn_of_gain_lt_one`).
* **The smooth loop** `smoothLoop`, whose kernel `Λ/(Λ + C)` has no step:
  its gain is closed-form (`hasDerivAt_smoothLoop_F`), and `λ(A−1) < C` is
  a one-line slope check certifying at most one equilibrium
  (`smoothLoop_fixedPt_unique`) and no bistable band
  (`smoothLoop_not_bistableOn`).
* **The queueing loop's gain**, concrete: `hasDerivAt_mm1Kernel` and
  `hasDerivAt_mm1Loop_F`, with the check run numerically on the band
  instance — gain below one at the healthy operating point
  (`mm1BandLoop_gain_lt_one`), above one near capacity
  (`one_lt_mm1BandLoop_gain`).
* **Continuous time**: for a trajectory `x` hypothesized to satisfy
  `x' t = F (x t) - x t`, the clamp condition forces strict decrease at or
  above the threshold (`BoundedLoop.clamp_fluid_strictAnti`); a drift bound
  `−δ` drains the backlog to zero within `x t₀ / δ` seconds
  (`fluid_drain_le`, `fluid_drain_clears`); gain at most `L` above an
  equilibrium decays the excursion at rate `1 − L`
  (`fluid_decay_of_gain_le`, derivative-read as `fluid_decay_of_deriv_le`,
  witnessed tight by `fluid_decay_witness`), and the spike is back within
  `ε` after `log((x t₀ − Λ₀)/ε)/(1 − L)` seconds
  (`fluid_recovery_within`).
* **The smooth loop's trajectory, supplied**: `x' = F(x) - x` has a local
  solution by Picard–Lindelöf (`smoothLoop_exists_trajectory`, through the
  Lipschitz modulus `lipschitzOnWith_smoothLoop_F`), and under the clamp
  condition `λ·A < Θ` that trajectory, while at or above the threshold,
  loses at least `Θ − λ·A` per second (`smoothLoop_fluid_drain`, pinned by
  `smoothDemoLoop_fluid_drain_pin`).

Scope: the general trajectory statements take the trajectory as a
hypothesis. For the smooth loop the trajectory is supplied:
`smoothLoop_exists_trajectory` proves local existence of a solution of
`x' = F(x) - x` by Picard–Lindelöf, with `lipschitzOnWith_smoothLoop_F` as
the modulus. Uniqueness, extension past the local interval, and existence
for any other loop are not claimed.
Derivative hypotheses use Mathlib's `deriv` and `HasDerivAt`; a strict
lower bound on `deriv F` implies differentiability (a non-differentiable
point has `deriv F x = 0`), so only the gain-below-one results carry an
explicit differentiability hypothesis.
-/

@[expose] public section

namespace Overload

/-!
## Amplification sensitivity
-/

/-- The sensitivity of the truncated-geometric response to its failure
probability: the termwise derivative `∑_{k<n} k·p^{k-1}` of
`expAttempts · n`. `hasDerivAt_expAttempts` certifies that it is the
derivative. The `k = 0` term is `0`: its `k` factor kills the
`ℕ`-truncated exponent `0 - 1 = 0`, matching the zero derivative of the
constant `p^0` term. -/
def expAttemptsDeriv (p : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, k * p ^ (k - 1)

/-- `expAttempts · n` has derivative `expAttemptsDeriv p n` at every real
`p`: termwise differentiation of the finite geometric sum. -/
theorem hasDerivAt_expAttempts (p : ℝ) (n : ℕ) :
    HasDerivAt (fun q => expAttempts q n) (expAttemptsDeriv p n) p := by
  unfold expAttempts expAttemptsDeriv
  exact HasDerivAt.fun_sum fun k _ => hasDerivAt_pow k p

/-- The sensitivity has a floor: with a second attempt allowed, it is at
least `1` for `0 ≤ p` — the `k = 1` term contributes `1` and every other
term is nonnegative. The calculus mirror of the first-order sandwich
`one_add_le_expAttempts`. -/
theorem one_le_expAttemptsDeriv {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ expAttemptsDeriv p n := by
  have h := Finset.single_le_sum (f := fun k : ℕ => (k : ℝ) * p ^ (k - 1))
    (fun k _ => mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hp _))
    (Finset.mem_range.mpr (by omega : 1 < n))
  simpa [expAttemptsDeriv] using h

/-- **The amplification flag** `h'(p) > 0`: a truncated-geometric response
with `2 ≤ n` has strictly positive sensitivity at every `0 ≤ p`. There is no
operating point at which such a response is insensitive to its failure
probability. -/
theorem expAttemptsDeriv_pos {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 2 ≤ n) :
    0 < expAttemptsDeriv p n :=
  lt_of_lt_of_le zero_lt_one (one_le_expAttemptsDeriv hp hn)

/-- Numeric pin of the amplification flag at a four-attempt response and a
failure probability of `1/2`. It records that the flag fires, not the value
it fires at. -/
theorem expAttemptsDeriv_pos_half_four : 0 < expAttemptsDeriv (1 / 2) 4 :=
  expAttemptsDeriv_pos (by norm_num) (by norm_num)

/-!
## The loop gain by the chain rule
-/

/-- **The loop gain**: if the kernel has derivative `g'` at `Λ` and the
response has derivative `h'` at `g Λ`, the demand operator has derivative
`λ·(h'·g')` at `Λ`. This is the scalar the gain flags below compare against
`1`, through `deriv`. -/
theorem BoundedLoop.hasDerivAt_F (L : BoundedLoop) {Λ g' h' : ℝ}
    (hg : HasDerivAt L.g g' Λ) (hh : HasDerivAt L.h h' (L.g Λ)) :
    HasDerivAt L.F (L.lam * (h' * g')) Λ :=
  (hh.comp Λ hg).const_mul L.lam

/-!
## The gain flags
-/

/-- **The gain flag, risky side** `F'(Λ) > 1`: at a fixed point `Λ₀` with
gain above `1` on the surrounding open interval, the fixed point repels —
strictly below `Λ₀` the map pushes down (`F x < x`), strictly above it
pushes up (`x < F x`), so a demand perturbation above `Λ₀` is amplified
rather than restored. Proof: `F - id` has positive derivative, hence is
strictly monotone on `[a, b]`, and vanishes at `Λ₀`. -/
theorem gain_gt_one_repels {F : ℝ → ℝ} {a b Λ₀ : ℝ}
    (hmem : Λ₀ ∈ Set.Icc a b) (hfix : Function.IsFixedPt F Λ₀)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hgain : ∀ x ∈ Set.Ioo a b, 1 < deriv F x) :
    (∀ x ∈ Set.Icc a b, x < Λ₀ → F x < x) ∧
      (∀ x ∈ Set.Icc a b, Λ₀ < x → x < F x) := by
  have hmono : StrictMonoOn (fun y => F y - y) (Set.Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b)
      (hcont.sub continuousOn_id) fun x hx => ?_
    rw [interior_Icc] at hx
    have hdF : DifferentiableAt ℝ F x :=
      differentiableAt_of_deriv_ne_zero
        (ne_of_gt (lt_trans zero_lt_one (hgain x hx)))
    have hG : HasDerivAt (fun y => F y - y) (deriv F x - 1) x :=
      hdF.hasDerivAt.sub (hasDerivAt_id x)
    rw [hG.deriv]
    have := hgain x hx
    linarith
  have hfeq : F Λ₀ = Λ₀ := hfix
  constructor
  · intro x hx hlt
    have := hmono hx hmem hlt
    simp only at this
    linarith
  · intro x hx hlt
    have := hmono hmem hx hlt
    simp only at this
    linarith

/-- Pin of the repelling flag on the linear model `x ↦ 2x`, whose gain is `2`
everywhere and whose fixed point is `0`: on `[-1, 1]` the map pushes down
below the fixed point and up above it. -/
theorem gain_gt_one_repels_pin :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, x < 0 → 2 * x < x) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, (0 : ℝ) < x → x < 2 * x) :=
  gain_gt_one_repels (F := fun x => 2 * x) (Λ₀ := 0) (by norm_num)
    (show (2 : ℝ) * 0 = 0 by norm_num) (by fun_prop)
    (fun x _ => by simp)

/-- **The gain flag, safe side** `F'(Λ) < 1`: with gain below `1` on the
open interval and `F` continuous on the closed one and differentiable
inside, `F - id` is strictly decreasing, so `[a, b]` holds at most one
fixed point. Differentiability is a genuine hypothesis here — a
non-differentiable point has `deriv F x = 0 < 1` and would satisfy the gain
bound vacuously. -/
theorem fixedPt_unique_of_gain_lt_one {F : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn F (Set.Icc a b))
    (hdiff : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ F x)
    (hgain : ∀ x ∈ Set.Ioo a b, deriv F x < 1)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hfx : Function.IsFixedPt F x) (hfy : Function.IsFixedPt F y) : x = y := by
  have hanti : StrictAntiOn (fun z => F z - z) (Set.Icc a b) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b)
      (hcont.sub continuousOn_id) fun z hz => ?_
    rw [interior_Icc] at hz
    have hG : HasDerivAt (fun w => F w - w) (deriv F z - 1) z :=
      (hdiff z hz).hasDerivAt.sub (hasDerivAt_id z)
    rw [hG.deriv]
    have := hgain z hz
    linarith
  have hfex : F x = x := hfx
  have hfey : F y = y := hfy
  exact hanti.injOn hx hy (by rw [hfex, hfey, sub_self, sub_self])

/-- **Gain below one excludes bistability.** If the loop gain stays below
`1` across the interior of the demand envelope `[0, λ·Amax]`, with `F`
continuous on it and differentiable inside, the extremal equilibria
coincide: no bistable band of any width. The stylized `stepLoop` fails the
continuity hypothesis at `C`: `stepLoop_F_of_lt` and `stepLoop_F_of_ge`
give `λ` below capacity and `λ·A` at or above it, and
`stepLoop_bistable`'s `lam < C ≤ lam·A` forces `1 < A`, so the two values
differ. No declaration here states that; the eval lemmas are where a
reader checks it. -/
theorem ClosedLoop.not_bistableOn_of_gain_lt_one (L : ClosedLoop)
    (hcont : ContinuousOn L.F (Set.Icc 0 (L.lam * L.Amax)))
    (hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) (L.lam * L.Amax), DifferentiableAt ℝ L.F x)
    (hgain : ∀ x ∈ Set.Ioo (0 : ℝ) (L.lam * L.Amax), deriv L.F x < 1) :
    ¬BistableOn L.F 0 (L.lam * L.Amax) := by
  have hab : (0 : ℝ) ≤ L.lam * L.Amax :=
    mul_nonneg L.lam_nonneg (le_trans zero_le_one L.one_le_Amax)
  have heq : lfpIcc L.F 0 (L.lam * L.Amax) = gfpIcc L.F 0 (L.lam * L.Amax) :=
    fixedPt_unique_of_gain_lt_one hcont hdiff hgain
      (lfpIcc_mem_Icc hab L.F_mapsTo) (gfpIcc_mem_Icc hab L.F_mapsTo)
      (isFixedPt_lfpIcc hab L.F_monotoneOn_Icc L.F_mapsTo)
      (isFixedPt_gfpIcc hab L.F_monotoneOn_Icc L.F_mapsTo)
  change ¬lfpIcc L.F 0 (L.lam * L.Amax) < gfpIcc L.F 0 (L.lam * L.Amax)
  rw [heq]
  exact lt_irrefl _

/-!
## The smooth loop: stability by slope alone
-/

/-- The smooth stylized loop: the failure probability rises with
utilization as `Λ/(Λ + C)` — differentiable everywhere on `[0, ∞)`, no
step — and the response interpolates affinely from `1` to `A`, as in
`stepLoop`. The gain is available in closed form
(`hasDerivAt_smoothLoop_F`), so stability is a slope check rather than an
order argument. -/
noncomputable def smoothLoop (lam C A : ℝ) (hlam : 0 ≤ lam) (hC : 0 < C)
    (hA : 1 ≤ A) : ClosedLoop where
  lam := lam
  g := fun Λ => Λ / (Λ + C)
  h := fun p => 1 + p * (A - 1)
  Amax := A
  lam_nonneg := hlam
  g_mem := by
    intro x hx
    have hxC : 0 < x + C := by linarith
    exact ⟨div_nonneg hx hxC.le, by rw [div_le_one hxC]; linarith⟩
  g_mono := by
    intro x hx y _ hxy
    have hx0 : (0 : ℝ) ≤ x := hx
    have hxC : 0 < x + C := by linarith
    have hyC : 0 < y + C := by linarith [le_trans hx0 hxy]
    rw [div_le_div_iff₀ hxC hyC]
    nlinarith [mul_le_mul_of_nonneg_right hxy hC.le]
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

/-- The gain of the smooth loop, in closed form:
`F'(Λ) = λ·(A−1)·C/(Λ+C)²` at every `Λ ≥ 0`. -/
theorem hasDerivAt_smoothLoop_F {lam C A : ℝ} (hlam : 0 ≤ lam) (hC : 0 < C)
    (hA : 1 ≤ A) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    HasDerivAt (smoothLoop lam C A hlam hC hA).F
      (lam * ((A - 1) * (C / (Λ + C) ^ 2))) Λ := by
  have hne : Λ + C ≠ 0 := by positivity
  have hg : HasDerivAt (fun y : ℝ => y / (y + C)) (C / (Λ + C) ^ 2) Λ := by
    have hnum : HasDerivAt (fun y : ℝ => y) 1 Λ := hasDerivAt_id Λ
    have h : HasDerivAt (fun y : ℝ => y / (y + C))
        ((1 * (Λ + C) - Λ * 1) / (Λ + C) ^ 2) Λ := hnum.div (hnum.add_const C) hne
    simpa using h
  have hh : HasDerivAt (fun p : ℝ => 1 + p * (A - 1)) (A - 1)
      ((smoothLoop lam C A hlam hC hA).g Λ) := by
    have h : HasDerivAt (fun p : ℝ => 1 + p * (A - 1)) (1 * (A - 1))
        ((smoothLoop lam C A hlam hC hA).g Λ) :=
      (hasDerivAt_const_add_iff (1 : ℝ)).mpr ((hasDerivAt_id _).mul_const (A - 1))
    rwa [one_mul] at h
  exact (smoothLoop lam C A hlam hC hA).hasDerivAt_F hg hh

/-- The smooth loop's gain bound: when `λ(A−1) < C`, the slope of `F` stays
below one on all of `[0, ∞)` — its maximum `λ(A−1)/C` sits at `Λ = 0`. -/
theorem smoothLoop_deriv_lt_one {lam C A : ℝ} (hlam : 0 ≤ lam) (hC : 0 < C)
    (hA : 1 ≤ A) (hgain : lam * (A - 1) < C) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    deriv (smoothLoop lam C A hlam hC hA).F Λ < 1 := by
  rw [(hasDerivAt_smoothLoop_F hlam hC hA hΛ).deriv]
  have hdiv : C / (Λ + C) ^ 2 ≤ 1 / C := by
    rw [div_le_div_iff₀ (by positivity) hC]
    nlinarith
  have hlamA : 0 ≤ lam * (A - 1) := mul_nonneg hlam (sub_nonneg.mpr hA)
  calc lam * ((A - 1) * (C / (Λ + C) ^ 2))
      = lam * (A - 1) * (C / (Λ + C) ^ 2) := by ring
    _ ≤ lam * (A - 1) * (1 / C) := mul_le_mul_of_nonneg_left hdiv hlamA
    _ < 1 := by
        rw [mul_one_div, div_lt_one hC]
        exact hgain

/-- The smooth loop's operator is Lipschitz on `[0, ∞)` with constant
`λ(A−1)/C`: the mean value inequality applied to the closed-form gain
`λ(A−1)·C/(Λ+C)²` (`hasDerivAt_smoothLoop_F`), whose maximum over `[0, ∞)`
is `λ(A−1)/C` at `Λ = 0`. The modulus a Picard–Lindelöf construction for
the fluid equation `x' = F(x) − x` consumes. -/
theorem lipschitzOnWith_smoothLoop_F {lam C A : ℝ} (hlam : 0 ≤ lam)
    (hC : 0 < C) (hA : 1 ≤ A) :
    LipschitzOnWith (Real.toNNReal (lam * (A - 1) / C))
      (smoothLoop lam C A hlam hC hA).F (Set.Ici 0) := by
  have hlamA : 0 ≤ lam * (A - 1) := mul_nonneg hlam (sub_nonneg.mpr hA)
  refine (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun Λ => lam * ((A - 1) * (C / (Λ + C) ^ 2)))
    (fun x hx => (hasDerivAt_smoothLoop_F hlam hC hA hx).hasDerivWithinAt)
    (fun x hx => ?_)
  have hx0 : (0 : ℝ) ≤ x := hx
  have hnonneg : 0 ≤ lam * ((A - 1) * (C / (x + C) ^ 2)) := by
    have : 0 ≤ A - 1 := sub_nonneg.mpr hA
    positivity
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    Real.coe_toNNReal _ (div_nonneg hlamA hC.le), abs_of_nonneg hnonneg]
  have hdiv : C / (x + C) ^ 2 ≤ 1 / C := by
    rw [div_le_div_iff₀ (by positivity) hC]
    nlinarith
  calc lam * ((A - 1) * (C / (x + C) ^ 2))
      = lam * (A - 1) * (C / (x + C) ^ 2) := by ring
    _ ≤ lam * (A - 1) * (1 / C) := mul_le_mul_of_nonneg_left hdiv hlamA
    _ = lam * (A - 1) / C := by ring

/-- **Stability by slope, uniqueness**: with `λ(A−1) < C` the smooth loop
has at most one equilibrium in its demand envelope — no order argument, no
Lipschitz constant, one derivative bound. -/
theorem smoothLoop_fixedPt_unique {lam C A : ℝ} (hlam : 0 ≤ lam) (hC : 0 < C)
    (hA : 1 ≤ A) (hgain : lam * (A - 1) < C) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 (lam * A)) (hy : y ∈ Set.Icc 0 (lam * A))
    (hfx : Function.IsFixedPt (smoothLoop lam C A hlam hC hA).F x)
    (hfy : Function.IsFixedPt (smoothLoop lam C A hlam hC hA).F y) : x = y :=
  fixedPt_unique_of_gain_lt_one
    (fun _ hz => (hasDerivAt_smoothLoop_F hlam hC hA
      hz.1).differentiableAt.continuousAt.continuousWithinAt)
    (fun _ hz => (hasDerivAt_smoothLoop_F hlam hC hA
      hz.1.le).differentiableAt)
    (fun _ hz => smoothLoop_deriv_lt_one hlam hC hA hgain hz.1.le)
    hx hy hfx hfy

/-- **Stability by slope, no band**: the same slope check in the phase
language — the smooth loop with `λ(A−1) < C` is not bistable on its
envelope. Also the satisfiability witness for
`not_bistableOn_of_gain_lt_one`'s hypothesis bundle, with a genuinely
load-coupled `F`. -/
theorem smoothLoop_not_bistableOn {lam C A : ℝ} (hlam : 0 ≤ lam) (hC : 0 < C)
    (hA : 1 ≤ A) (hgain : lam * (A - 1) < C) :
    ¬BistableOn (smoothLoop lam C A hlam hC hA).F 0 (lam * A) :=
  (smoothLoop lam C A hlam hC hA).not_bistableOn_of_gain_lt_one
    (fun _ hz => (hasDerivAt_smoothLoop_F hlam hC hA
      hz.1).differentiableAt.continuousAt.continuousWithinAt)
    (fun _ hz => (hasDerivAt_smoothLoop_F hlam hC hA
      hz.1.le).differentiableAt)
    (fun _ hz => smoothLoop_deriv_lt_one hlam hC hA hgain hz.1.le)

/-- Numeric pin of the uniqueness leg at the same numbers: with `λ(A−1) = 10`
under `C = 20`, the demand levels `10` and `20` cannot both be equilibria —
the slope check leaves at most one, and these are two. -/
theorem smoothDemoLoop_fixedPt_unique_pin :
    ¬(Function.IsFixedPt (smoothLoop 10 20 2 (by norm_num) (by norm_num)
        (by norm_num)).F 10 ∧
      Function.IsFixedPt (smoothLoop 10 20 2 (by norm_num) (by norm_num)
        (by norm_num)).F 20) := by
  rintro ⟨h10, h20⟩
  have h : (10 : ℝ) = 20 :=
    smoothLoop_fixedPt_unique (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h10 h20
  norm_num at h

/-- Numeric pin of the slope check on a concrete smooth loop: at `λ = 10`,
`C = 20`, `A = 2` the gain bound is `λ(A−1) = 10 < 20 = C`, so the loop
carries no bistable band on `[0, 20]`. `mm1FlatLoop_not_bistable` reaches
the same conclusion from a constant kernel; here the kernel is load-coupled
and the slope bound alone rules the band out. -/
theorem smoothDemoLoop_not_bistableOn :
    ¬BistableOn (smoothLoop 10 20 2 (by norm_num) (by norm_num)
      (by norm_num)).F 0 (10 * 2) :=
  smoothLoop_not_bistableOn (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-!
## The gain on the queueing loop
-/

/-- Below capacity the M/M/1 kernel is differentiable with derivative
`τ·e^{-(C-Λ)τ}`: the sojourn tail steepens as headroom shrinks. Away from
the saturation point the piecewise definition is locally the exponential,
so the derivative transfers by local agreement. -/
theorem hasDerivAt_mm1Kernel {C τ Λ : ℝ} (hΛ : Λ < C) :
    HasDerivAt (mm1Kernel C τ) (τ * Real.exp (-((C - Λ) * τ))) Λ := by
  have hinner : HasDerivAt (fun y : ℝ => -((C - y) * τ)) τ Λ := by
    have h : HasDerivAt (fun y : ℝ => -((C - y) * τ)) (-(-1 * τ)) Λ :=
      (((hasDerivAt_id Λ).const_sub C).mul_const τ).neg
    simpa using h
  have hsmooth : HasDerivAt (fun y : ℝ => Real.exp (-((C - y) * τ)))
      (τ * Real.exp (-((C - Λ) * τ))) Λ := by
    convert hinner.exp using 1
    ring
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hΛ] with y hy
  exact mm1Kernel_of_lt hy

/-- **The loop gain of the M/M/1 loop, computed.** Below capacity,
`F' = λ·h'(g Λ)·g'(Λ)` assembles by the chain rule from
`hasDerivAt_expAttempts` and `hasDerivAt_mm1Kernel`: the sensitivity of the
response at the operating failure probability, times the steepening of the
sojourn tail, scaled by the offered load. -/
theorem hasDerivAt_mm1Loop_F {lam C τ Λ : ℝ} {m : ℕ} (hlam : 0 ≤ lam)
    (hτ : 0 ≤ τ) (hm : 1 ≤ m) (hΛ : Λ < C) :
    HasDerivAt (mm1Loop lam C τ m hlam hτ hm).F
      (lam * (expAttemptsDeriv (mm1Kernel C τ Λ) m *
        (τ * Real.exp (-((C - Λ) * τ))))) Λ :=
  (mm1Loop lam C τ m hlam hτ hm).hasDerivAt_F (hasDerivAt_mm1Kernel hΛ)
    (hasDerivAt_expAttempts _ m)

/-- The streamlined check, safe side, on the band instance: at the healthy
operating point (demand 31) the loop gain of `mm1BandLoop` is below one.
The tail `p = e^{-69}` is at most `1/70` (`exp_neg_le_inv_one_add`), so the
gain `30·(1 + 2p + 3p²)·p` is far below one. -/
theorem mm1BandLoop_gain_lt_one : deriv mm1BandLoop.F 31 < 1 := by
  have hd : HasDerivAt mm1BandLoop.F
      (30 * (expAttemptsDeriv (mm1Kernel 100 1 31) 4 *
        (1 * Real.exp (-((100 - 31) * 1))))) 31 :=
    hasDerivAt_mm1Loop_F (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  rw [hd.deriv]
  have hE : Real.exp (-((100 - (31 : ℝ)) * 1)) = Real.exp (-69) := by
    norm_num
  have hp : mm1Kernel 100 1 31 = Real.exp (-69) := by
    rw [mm1Kernel_of_lt (by norm_num)]
    norm_num
  rw [hE, hp]
  have hderiv : expAttemptsDeriv (Real.exp (-69)) 4
      = 1 + 2 * Real.exp (-69) + 3 * Real.exp (-69) ^ 2 := by
    norm_num [expAttemptsDeriv, Finset.sum_range_succ]
  rw [hderiv]
  have hp0 : (0 : ℝ) < Real.exp (-69) := Real.exp_pos _
  have hp70 : Real.exp (-69 : ℝ) ≤ 1 / 70 := by
    have h := exp_neg_le_inv_one_add (x := 69) (by norm_num)
    norm_num at h
    linarith
  have hp2 : Real.exp (-69 : ℝ) ^ 2 ≤ (1 / 70) ^ 2 :=
    pow_le_pow_left₀ hp0.le hp70 2
  have step : (1 + 2 * Real.exp (-69) + 3 * Real.exp (-69) ^ 2) *
      Real.exp (-69) ≤ (1 + 2 * (1 / 70) + 3 * (1 / 70) ^ 2) * (1 / 70) :=
    mul_le_mul (by linarith) hp70 hp0.le (by norm_num)
  nlinarith [step]

/-- The streamlined check, risky side, on the same instance: near capacity
(demand 99, headroom 1) the loop gain of `mm1BandLoop` exceeds one. The
tail is `e^{-1} > 1/3` (from `exp_one_lt_d9`), the response sensitivity is
at least `1` (`one_le_expAttemptsDeriv`), and `30·1·(1/3) = 10`. One loop,
both flags. -/
theorem one_lt_mm1BandLoop_gain : 1 < deriv mm1BandLoop.F 99 := by
  have hd : HasDerivAt mm1BandLoop.F
      (30 * (expAttemptsDeriv (mm1Kernel 100 1 99) 4 *
        (1 * Real.exp (-((100 - 99) * 1))))) 99 :=
    hasDerivAt_mm1Loop_F (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  rw [hd.deriv]
  have hp1 : (-((100 - 99 : ℝ) * 1)) = -1 := by norm_num
  rw [hp1]
  have hp3 : (1 : ℝ) / 3 < Real.exp (-1) := by
    have h3 : Real.exp 1 < 3 :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    norm_num [h3]
  have hgain1 : 1 ≤ expAttemptsDeriv (mm1Kernel 100 1 99) 4 :=
    one_le_expAttemptsDeriv
      ((mm1Kernel_mem (by norm_num) 99 (by norm_num)).1) (by norm_num)
  have hp0 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have key : (1 : ℝ) / 3 < expAttemptsDeriv (mm1Kernel 100 1 99) 4 *
      Real.exp (-1) :=
    lt_of_lt_of_le hp3
      (le_mul_of_one_le_left hp0.le hgain1)
  linarith

/-!
## The drift in continuous time
-/

/-- **The clamp theorem in continuous time.** Under the clamp `h ≤ K` with
`λ·K < Θ` and `0 ≤ Θ` (the nonnegativity that puts `x t` in the kernel's
domain), a trajectory satisfying `x' t = F (x t) - x t` strictly
decreases on any interval it spends at or above the threshold: the drift
there is at most `λ·K - Θ < 0`. Conditioned on the trajectory staying in
the region — no invariance or exit-time claim is made. -/
theorem BoundedLoop.clamp_fluid_strictAnti (L : BoundedLoop)
    {K Θ t₀ t₁ : ℝ} {x : ℝ → ℝ}
    (hclamp : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p ≤ K) (hK : L.lam * K < Θ)
    (hΘ : 0 ≤ Θ)
    (hx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt x (L.F (x t) - x t) t)
    (hreg : ∀ t ∈ Set.Icc t₀ t₁, Θ ≤ x t) :
    StrictAntiOn x (Set.Icc t₀ t₁) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc t₀ t₁)
    (fun t ht => (hx t ht).differentiableAt.continuousAt.continuousWithinAt)
    fun t ht => ?_
  rw [interior_Icc] at ht
  have ht' : t ∈ Set.Icc t₀ t₁ := Set.Ioo_subset_Icc_self ht
  rw [(hx t ht').deriv]
  have hx0 : 0 ≤ x t := le_trans hΘ (hreg t ht')
  have hF : L.F (x t) ≤ L.lam * K :=
    mul_le_mul_of_nonneg_left (hclamp _ (L.g_mem _ hx0)) L.lam_nonneg
  have := hreg t ht'
  linarith

/-- Pin of the drift sign at a clamp with nothing offered: at `λ = 0` the
demand operator is identically zero, so `λ·K = 0` sits below the threshold
`1`, and the trajectory `x t = 100·e^{−t}` — which solves `x' = F(x) − x`
there — stays above `1` throughout `[0, 1]` and strictly decreases on it. -/
theorem clamp_fluid_strictAnti_pin :
    StrictAntiOn (fun t : ℝ => 100 * Real.exp (-t)) (Set.Icc 0 1) := by
  have hexp1 : Real.exp 1 < 100 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  refine (stepLoop 0 5 2 (by norm_num)
    (by norm_num)).toBoundedLoop.clamp_fluid_strictAnti (K := 2) (Θ := 1)
    (fun p hp => by
      change (1 : ℝ) + p * (2 - 1) ≤ 2
      linarith [hp.2])
    (show (0 : ℝ) * 2 < 1 by norm_num) zero_le_one (fun t _ => ?_)
    (fun t ht => ?_)
  · have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    change HasDerivAt (fun s : ℝ => 100 * Real.exp (-s))
      ((0 : ℝ) * (1 + stepKernel 5 (100 * Real.exp (-t)) * (2 - 1))
        - 100 * Real.exp (-t)) t
    rw [show (0 : ℝ) * (1 + stepKernel 5 (100 * Real.exp (-t)) * (2 - 1))
      - 100 * Real.exp (-t) = 100 * -Real.exp (-t) by ring]
    exact hexp.const_mul 100
  · have hmono : Real.exp (-1) ≤ Real.exp (-t) :=
      Real.exp_le_exp.mpr (by linarith [ht.2])
    have hstep := mul_lt_mul_of_pos_left hexp1 (Real.exp_pos (-1))
    rw [hmul] at hstep
    linarith

/-- **The continuous drain bound**: a trajectory whose drift is at most
`−δ` loses at least `δ` per second — `x t ≤ x t₀ − δ·(t − t₀)` — by the
mean value bound on the interval. -/
theorem fluid_drain_le {δ t₀ t₁ : ℝ} {x v : ℝ → ℝ}
    (hx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Set.Icc t₀ t₁, v t ≤ -δ) :
    ∀ t ∈ Set.Icc t₀ t₁, x t ≤ x t₀ - δ * (t - t₀) := by
  intro t ht
  have h := (convex_Icc t₀ t₁).image_sub_le_mul_sub_of_deriv_le
    (fun s hs => (hx s hs).differentiableAt.continuousAt.continuousWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs
      exact (hx s
        (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      rw [(hx s hs').deriv]
      exact hv s hs')
    t₀ (Set.left_mem_Icc.mpr (le_trans ht.1 ht.2)) t ht ht.1
  linarith

/-- **The recovery time, in seconds**: with drain rate at least `δ > 0`,
the backlog `x t₀` is gone once `x t₀ / δ` seconds have passed — the
recovery integral `T_rec = Q₀/(C − a_res)` priced on the trajectory itself,
with no discrete ceiling and no simulation. The drain rate is a lower
bound, so `x t₀ / δ` is a sufficient time rather than the earliest one. -/
theorem fluid_drain_clears {δ t₀ t₁ : ℝ} {x v : ℝ → ℝ} (hδ : 0 < δ)
    (hx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Set.Icc t₀ t₁, v t ≤ -δ) :
    ∀ t ∈ Set.Icc t₀ t₁, t₀ + x t₀ / δ ≤ t → x t ≤ 0 := by
  intro t ht htime
  have h := fluid_drain_le hx hv t ht
  have h2 : x t₀ / δ ≤ t - t₀ := by linarith
  have h3 := (div_le_iff₀ hδ).mp h2
  linarith

/-- Numeric pin of the recovery integral at `12/3 = 4`: the trajectory
`12 − 3t`, whose drift is exactly `−3`, is at zero by second `4`. The
continuous replacement for the discrete `Q k = 12 − 3k` regression that
went with the old drain bound. -/
theorem fluid_drain_twelve_clears_at_four :
    (fun t : ℝ => 12 - 3 * t) 4 ≤ 0 := by
  refine fluid_drain_clears (δ := 3) (t₀ := 0) (t₁ := 10) (v := fun _ => -3)
    (x := fun t : ℝ => 12 - 3 * t)
    (by norm_num) (fun t _ => ?_) (fun _ _ => le_rfl) 4 (by norm_num)
    (by norm_num)
  have h : HasDerivAt (fun t : ℝ => 12 - 3 * t) (-(3 * 1)) t :=
    (HasDerivAt.const_mul (3 : ℝ) (hasDerivAt_id t)).const_sub 12
  convert h using 1
  norm_num

/-- **The fluid equation has a trajectory.** For every positive initial
backlog `x₀`, the smooth loop's fluid equation `x' = F(x) − x` has a local
solution: a trajectory `α` with `α t₀ = x₀` and derivative `F (α t) − α t`
at every `t` of a closed interval of positive length. Picard–Lindelöf
(Mathlib's `IsPicardLindelof`) on the ball `[0, 2x₀]`, with the Lipschitz
modulus from `lipschitzOnWith_smoothLoop_F`. Local existence only: the
interval length is existential, and neither uniqueness nor extension past
the interval is claimed. -/
theorem smoothLoop_exists_trajectory {lam C A x₀ : ℝ} (hlam : 0 ≤ lam)
    (hC : 0 < C) (hA : 1 ≤ A) (hx₀ : 0 < x₀) (t₀ : ℝ) :
    ∃ t₁, t₀ < t₁ ∧ ∃ α : ℝ → ℝ, α t₀ = x₀ ∧
      ∀ t ∈ Set.Icc t₀ t₁,
        HasDerivAt α ((smoothLoop lam C A hlam hC hA).F (α t) - α t) t := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hLb0 : 0 ≤ lam * A + 2 * x₀ :=
    add_nonneg (mul_nonneg hlam hA0) (by linarith)
  set ε : ℝ := x₀ / (lam * A + 2 * x₀ + 1) with hεdef
  have hε0 : 0 < ε := div_pos hx₀ (by linarith)
  have hball : Metric.closedBall x₀ x₀ = Set.Icc 0 (2 * x₀) := by
    rw [Real.closedBall_eq_Icc, sub_self, two_mul]
  have hlamA : 0 ≤ lam * (A - 1) / C :=
    div_nonneg (mul_nonneg hlam (sub_nonneg.mpr hA)) hC.le
  have hG : LipschitzOnWith (Real.toNNReal (lam * (A - 1) / C + 1))
      (fun x => (smoothLoop lam C A hlam hC hA).F x - x) (Set.Ici 0) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h1 := (lipschitzOnWith_smoothLoop_F hlam hC hA).dist_le_mul x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hlamA] at h1
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
    have h2 : (smoothLoop lam C A hlam hC hA).F x - x -
        ((smoothLoop lam C A hlam hC hA).F y - y) =
        ((smoothLoop lam C A hlam hC hA).F x -
          (smoothLoop lam C A hlam hC hA).F y) + -(x - y) := by
      ring
    calc |(smoothLoop lam C A hlam hC hA).F x - x -
        ((smoothLoop lam C A hlam hC hA).F y - y)|
        = |((smoothLoop lam C A hlam hC hA).F x -
            (smoothLoop lam C A hlam hC hA).F y) + -(x - y)| := by rw [h2]
      _ ≤ |(smoothLoop lam C A hlam hC hA).F x -
            (smoothLoop lam C A hlam hC hA).F y| + |-(x - y)| := abs_add_le _ _
      _ = |(smoothLoop lam C A hlam hC hA).F x -
            (smoothLoop lam C A hlam hC hA).F y| + |x - y| := by rw [abs_neg]
      _ ≤ lam * (A - 1) / C * |x - y| + |x - y| := by linarith
      _ = (lam * (A - 1) / C + 1) * |x - y| := by ring
  have hpl : IsPicardLindelof
      (fun _ x => (smoothLoop lam C A hlam hC hA).F x - x)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, by constructor <;> linarith⟩ x₀
      (Real.toNNReal x₀) 0 (Real.toNNReal (lam * A + 2 * x₀))
      (Real.toNNReal (lam * (A - 1) / C + 1)) := by
    refine ⟨fun t _ht => ?_, fun _x _hx => continuousOn_const,
      fun t _ht x hx => ?_, ?_⟩
    · refine hG.mono ?_
      rw [Real.coe_toNNReal _ hx₀.le, hball]
      exact fun z hz => hz.1
    · rw [Real.coe_toNNReal _ hx₀.le, hball] at hx
      rw [Real.coe_toNNReal _ hLb0, Real.norm_eq_abs, abs_le]
      have hFle : (smoothLoop lam C A hlam hC hA).F x ≤ lam * A :=
        (smoothLoop lam C A hlam hC hA).F_le hx.1
      have hF0 : 0 ≤ (smoothLoop lam C A hlam hC hA).F x :=
        (smoothLoop lam C A hlam hC hA).F_nonneg hx.1
      constructor
      · change -(lam * A + 2 * x₀) ≤ (smoothLoop lam C A hlam hC hA).F x - x
        linarith [hx.1, hx.2]
      · change (smoothLoop lam C A hlam hC hA).F x - x ≤ lam * A + 2 * x₀
        linarith [hx.1, hx.2, hx₀]
    · rw [Real.coe_toNNReal _ hLb0, Real.coe_toNNReal _ hx₀.le]
      change (lam * A + 2 * x₀) * max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) ≤ x₀ - 0
      rw [add_sub_cancel_left, sub_sub_cancel, max_self, sub_zero, hεdef]
      calc (lam * A + 2 * x₀) * (x₀ / (lam * A + 2 * x₀ + 1))
          ≤ (lam * A + 2 * x₀ + 1) * (x₀ / (lam * A + 2 * x₀ + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith)
              (div_nonneg hx₀.le (by linarith))
        _ = x₀ := by
            rw [mul_comm]
            exact div_mul_cancel₀ x₀ (by linarith)
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨t₀ + ε / 2, by linarith, α, hα0, fun t ht => ?_⟩
  exact (hα t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

/-- **The drain, priced on the system's own trajectory.** Under the clamp
condition `λ·A < Θ` (the smooth loop's response is bounded by `A`, so this
is the clamp certificate at `K = A`) and initial backlog `x₀` at or above
the threshold, a trajectory of `x' = F(x) − x` from `x₀` exists and,
conditioned on staying at or above `Θ`, loses at least `Θ − λ·A` per
second: `α t ≤ x₀ − (Θ − λ·A)(t − t₀)`. Existence from
`smoothLoop_exists_trajectory`; the rate from `fluid_drain_le`, because at
or above `Θ ≥ 0` the drift `F(α t) − α t` is at most `λ·A − Θ`. The
horizon `t₁` is existential, and nothing is claimed past it or below the
threshold. -/
theorem smoothLoop_fluid_drain {lam C A Θ x₀ : ℝ} (hlam : 0 ≤ lam)
    (hC : 0 < C) (hA : 1 ≤ A) (hΘ : lam * A < Θ) (hx₀ : Θ ≤ x₀) (t₀ : ℝ) :
    ∃ t₁, t₀ < t₁ ∧ ∃ α : ℝ → ℝ, α t₀ = x₀ ∧
      (∀ t ∈ Set.Icc t₀ t₁,
        HasDerivAt α ((smoothLoop lam C A hlam hC hA).F (α t) - α t) t) ∧
      ∀ t ∈ Set.Icc t₀ t₁, (∀ s ∈ Set.Icc t₀ t, Θ ≤ α s) →
        α t ≤ x₀ - (Θ - lam * A) * (t - t₀) := by
  have hlamA : 0 ≤ lam * A := mul_nonneg hlam (le_trans zero_le_one hA)
  have hx₀0 : 0 < x₀ := lt_of_le_of_lt hlamA (lt_of_lt_of_le hΘ hx₀)
  obtain ⟨t₁, ht₁, α, hα0, hα⟩ :=
    smoothLoop_exists_trajectory hlam hC hA hx₀0 t₀
  refine ⟨t₁, ht₁, α, hα0, hα, fun t ht hreg => ?_⟩
  have hsub : Set.Icc t₀ t ⊆ Set.Icc t₀ t₁ := Set.Icc_subset_Icc_right ht.2
  have hv : ∀ s ∈ Set.Icc t₀ t,
      (smoothLoop lam C A hlam hC hA).F (α s) - α s ≤ -(Θ - lam * A) := by
    intro s hs
    have hΘs := hreg s hs
    have h0s : 0 ≤ α s := le_trans (le_trans hlamA hΘ.le) hΘs
    have hFle : (smoothLoop lam C A hlam hC hA).F (α s) ≤ lam * A :=
      (smoothLoop lam C A hlam hC hA).F_le h0s
    linarith
  have hdrain := fluid_drain_le (δ := Θ - lam * A) (t₀ := t₀) (t₁ := t)
    (x := α)
    (v := fun s => (smoothLoop lam C A hlam hC hA).F (α s) - α s)
    (fun s hs => hα s (hsub hs)) hv t (Set.right_mem_Icc.mpr ht.1)
  rwa [hα0] at hdrain

/-- Numeric pin of the drain on a concrete smooth loop: `λ = 10`, `C = 20`,
`A = 2`, threshold `Θ = 25` — so `λ·A = 20 < 25` and the priced rate is
`Θ − λ·A = 5` per second — with initial backlog `30`. A trajectory from
`30` exists, and while it stays at or above `25` it obeys `α t ≤ 30 − 5t`.
Exercises the drain theorem's hypothesis bundle at closed numerals. -/
theorem smoothDemoLoop_fluid_drain_pin :
    ∃ t₁, (0 : ℝ) < t₁ ∧ ∃ α : ℝ → ℝ, α 0 = 30 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) t₁,
        HasDerivAt α ((smoothLoop 10 20 2 (by norm_num) (by norm_num)
          (by norm_num)).F (α t) - α t) t) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) t₁, (∀ s ∈ Set.Icc (0 : ℝ) t, 25 ≤ α s) →
        α t ≤ 30 - 5 * t := by
  obtain ⟨t₁, ht₁, α, hα0, hα, hdrain⟩ :=
    smoothLoop_fluid_drain (lam := 10) (C := 20) (A := 2) (Θ := 25)
      (x₀ := 30) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) 0
  refine ⟨t₁, ht₁, α, hα0, hα, fun t ht hreg => ?_⟩
  have h := hdrain t ht hreg
  norm_num at h
  linarith

/-- **The gain margin is a decay rate.** If along the trajectory the map's
excursion above `Λ₀` is bounded by a gain `L` — `F (x t) - Λ₀ ≤ L·(x t - Λ₀)`
— then the distance to `Λ₀` obeys
`x t - Λ₀ ≤ (x t₀ - Λ₀)·exp(-(1-L)·(t-t₀))`. Read at a fixed point `Λ₀`
with `L < 1`: return toward equilibrium at least exponentially fast, with
the gain margin `1 - L` as the rate. The inequality itself needs neither
`L < 1` nor `Λ₀ ≤ x t`. This is Grönwall's inequality instantiated: Mathlib's
`le_gronwallBound_of_liminf_deriv_right_le` at `K = -(1 - L)` and `ε = 0`,
where `gronwallBound_ε0` collapses the bound to `δ·exp(K·x)`. The excursion
`x t - Λ₀` is the `f` it bounds, and the gain hypothesis is what supplies its
`f' ≤ K·f` boundary condition. -/
theorem fluid_decay_of_gain_le {F : ℝ → ℝ} {L Λ₀ t₀ t₁ : ℝ} {x : ℝ → ℝ}
    (hgain : ∀ t ∈ Set.Icc t₀ t₁, F (x t) - Λ₀ ≤ L * (x t - Λ₀))
    (hx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt x (F (x t) - x t) t) :
    ∀ t ∈ Set.Icc t₀ t₁,
      x t - Λ₀ ≤ (x t₀ - Λ₀) * Real.exp (-((1 - L) * (t - t₀))) := by
  have hd : ∀ t ∈ Set.Icc t₀ t₁,
      HasDerivAt (fun s => x s - Λ₀) (F (x t) - x t) t :=
    fun t ht => (hasDerivAt_sub_const_iff Λ₀).mpr (hx t ht)
  have key := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun s => x s - Λ₀) (f' := fun s => F (x s) - x s)
    (δ := x t₀ - Λ₀) (K := -(1 - L)) (ε := 0) (a := t₀) (b := t₁)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs _ hr =>
      (hd s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl
    (fun s hs => by
      have h := hgain s (Set.Ico_subset_Icc_self hs)
      nlinarith [h])
  intro t ht
  have h := key t ht
  rwa [gronwallBound_ε0, neg_mul] at h

/-- The decay bound with the gain read off the derivative: at a fixed point
`Λ₀` of `F`, with `F` continuous on `[a, b]`, differentiable on `(a, b)`,
and `deriv F ≤ L` there, a trajectory of `x' = F(x) - x` that stays in
`[a, b]` at or above `Λ₀` obeys the bound of `fluid_decay_of_gain_le`:
`Convex.image_sub_le_mul_sub_of_deriv_le` converts the derivative bound
into the excursion bound that theorem consumes. -/
theorem fluid_decay_of_deriv_le {F : ℝ → ℝ} {L a b Λ₀ t₀ t₁ : ℝ} {x : ℝ → ℝ}
    (hmem : Λ₀ ∈ Set.Icc a b) (hfix : Function.IsFixedPt F Λ₀)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ F (Set.Ioo a b))
    (hL : ∀ z ∈ Set.Ioo a b, deriv F z ≤ L)
    (hx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt x (F (x t) - x t) t)
    (hin : ∀ t ∈ Set.Icc t₀ t₁, x t ∈ Set.Icc a b)
    (habove : ∀ t ∈ Set.Icc t₀ t₁, Λ₀ ≤ x t) :
    ∀ t ∈ Set.Icc t₀ t₁,
      x t - Λ₀ ≤ (x t₀ - Λ₀) * Real.exp (-((1 - L) * (t - t₀))) := by
  refine fluid_decay_of_gain_le (fun t ht => ?_) hx
  have hfeq : F Λ₀ = Λ₀ := hfix
  have h := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hcont
    (by rw [interior_Icc]; exact hdiff)
    (fun z hz => by rw [interior_Icc] at hz; exact hL z hz)
    Λ₀ hmem (x t) (hin t ht) (habove t ht)
  rw [hfeq] at h
  exact h

/-- **Spike recovery time, in seconds**: under gain at most `L` above the
equilibrium `Λ₀`, an excursion is back within `ε` of `Λ₀` once
`log((x t₀ − Λ₀)/ε) / (1 − L)` seconds have passed. Inverting the
exponential of `fluid_decay_of_gain_le` — the spike-recovery arithmetic
priced in seconds rather than simulated. The bound is a sufficient time,
not the earliest one. -/
theorem fluid_recovery_within {F : ℝ → ℝ} {L Λ₀ t₀ t₁ ε : ℝ} {x : ℝ → ℝ}
    (hL : L < 1) (hε : 0 < ε)
    (hgain : ∀ t ∈ Set.Icc t₀ t₁, F (x t) - Λ₀ ≤ L * (x t - Λ₀))
    (hx : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt x (F (x t) - x t) t) :
    ∀ t ∈ Set.Icc t₀ t₁,
      t₀ + Real.log ((x t₀ - Λ₀) / ε) / (1 - L) ≤ t → x t - Λ₀ ≤ ε := by
  intro t ht htime
  have hdecay := fluid_decay_of_gain_le hgain hx t ht
  have h1L : 0 < 1 - L := by linarith
  rcases le_or_gt (x t₀ - Λ₀) 0 with hD | hD
  · nlinarith [hdecay, Real.exp_pos (-((1 - L) * (t - t₀)))]
  · have h2 : Real.log ((x t₀ - Λ₀) / ε) ≤ (1 - L) * (t - t₀) := by
      have h3 : Real.log ((x t₀ - Λ₀) / ε) / (1 - L) ≤ t - t₀ := by linarith
      linarith [(div_le_iff₀ h1L).mp h3]
    have hεD : 0 < ε / (x t₀ - Λ₀) := div_pos hε hD
    have hexp : Real.exp (-((1 - L) * (t - t₀))) ≤ ε / (x t₀ - Λ₀) := by
      rw [← Real.le_log_iff_exp_le hεD, ← inv_div, Real.log_inv]
      linarith
    calc x t - Λ₀ ≤ (x t₀ - Λ₀) * Real.exp (-((1 - L) * (t - t₀))) := hdecay
      _ ≤ (x t₀ - Λ₀) * (ε / (x t₀ - Λ₀)) :=
          mul_le_mul_of_nonneg_left hexp hD.le
      _ = ε := by field_simp

/-- Numeric pin of the spike-recovery time: a unit excursion above the
equilibrium, held at gain `0`, is within `1/2` after `log 2` seconds, and
second `1` is past that. The trajectory `e^{-s}` under the operator `F ≡ 0`
is the pair `fluid_decay_witness` uses; here the bound is slack rather than
attained, so the pin exercises the log inversion. -/
theorem fluid_recovery_within_half : Real.exp (-1 : ℝ) - 0 ≤ 1 / 2 := by
  refine fluid_recovery_within (F := fun _ => (0 : ℝ)) (L := 0) (Λ₀ := 0)
    (t₀ := 0) (t₁ := 1) (ε := 1 / 2) (x := fun s => Real.exp (-s))
    (by norm_num) (by norm_num) (fun t _ => by norm_num)
    (fun t _ => ?_) 1 (by norm_num) ?_
  · have h := ((hasDerivAt_id t).neg).exp
    change HasDerivAt (fun s : ℝ => Real.exp (-s)) (0 - Real.exp (-t)) t
    have hval : (0 : ℝ) - Real.exp (-t) = Real.exp (-t) * (-1) := by ring
    rw [hval]
    exact h
  · have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    norm_num
    linarith

/-- Witness that the decay hypotheses are satisfiable, with the bound
tight: `x s = e^{-s}` is a genuine motion solving `x' = F(x) - x` for the
constant operator `F ≡ 0`, whose fixed point is `Λ₀ = 0` with gain `L = 0`;
it stays in `[0, 1]` for `t ∈ [0, 1]`, and the bound of
`fluid_decay_of_deriv_le` specializes to `e^{-t} ≤ e^{-t}` — attained, not
merely respected. -/
theorem fluid_decay_witness :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.exp (-t) - 0 ≤
        (Real.exp (-0) - 0) * Real.exp (-((1 - 0) * (t - 0))) := by
  refine fluid_decay_of_deriv_le (F := fun _ => (0 : ℝ)) (a := 0) (b := 1)
    ⟨le_rfl, zero_le_one⟩ rfl continuousOn_const
    ((differentiable_const (0 : ℝ)).differentiableOn) (fun z _ => by simp)
    (fun t _ => ?_) (fun t ht => ?_) (fun t _ => (Real.exp_pos (-t)).le)
  · have h := ((hasDerivAt_id t).neg).exp
    have hval : (fun _ => (0 : ℝ)) (Real.exp (-t)) - Real.exp (-t)
        = Real.exp (-t) * (-1) := by norm_num
    rw [hval]
    exact h
  · exact ⟨(Real.exp_pos (-t)).le,
      Real.exp_le_one_iff.mpr (by linarith [ht.1])⟩

end Overload
