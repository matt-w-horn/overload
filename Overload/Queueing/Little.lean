module

public import Overload.Basic -- shake: keep
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

/-!
# Little's law, deterministic sample-path form

The mean-value bridge `L = λW` used definitionally by `MM1.lean` is,
at its core, not a stochastic fact: Stidham's sample-path theorem derives
it for a single deterministic trace from two rate hypotheses alone. This
file proves that form.

A `SamplePath` is a trace of arrival instants `a` (ordered) and departure
instants `d` — deliberately **not** assumed ordered, so overtaking
disciplines (LIFO, priorities) are covered. Under

* **H1** (arrival rate): `a n / n → τ` with `0 < τ` (so `λ = 1/τ`), and
* **H2** (Cesàro sojourn mean): `(∑_{k<n} W k) / n → Wbar`,

the long-run time-average number in system exists and equals `λ·Wbar`
(`SamplePath.little`): `area t / t → Wbar/τ`, where `area t` is cumulative
occupancy before `t`, expressed customer-by-customer — each summand
`timeIn t n` is the length of `[aₙ, dₙ) ∩ [0, t)`, so `area` is the area
under the number-in-system step function with no integral required.

No distributions, no independence, no stationarity, no ergodicity. The
technical care sits exactly where the classical proof puts it: departures
need not be monotone, so the departed side runs through the longest
fully-departed *prefix* (`departedPrefix`), and the count asymptotics are
proved once, for any counting function satisfying two one-sided bounds
(`count_div_tendsto`) — by squeeze and composition, with no ε-management.
Byproducts stated separately: the Cesàro tail bound `W n / n → 0`
(`tendsto_W_div`) and the departure rate `d n / n → τ`
(`tendsto_d_div`).

Brumelle's generalization `H = λG` rides the same sandwich: give
customer `n` a nonnegative weight `g n` — value accrued at constant
rate while in system — and the weighted occupancy time-average
equals `λ·Gbar` (`SamplePath.brumelle`), with the value analogue of H2
as the one extra hypothesis; `little` is recovered at unit weight
(`little_of_brumelle`).

What this does **not** claim: connecting these time averages to the
stationary quantities of `MM1.lean` (`meanQueue`, `meanWait`) is an
ergodic identification, deliberately left as the documented definitional
bridge there.
-/

@[expose] public section

open Filter

namespace Overload

/-- A deterministic trace of one queueing system: customer `n` arrives at
`a n` and departs at `d n`. Arrivals are indexed in order; departures are
deliberately **not** ordered — overtaking disciplines (LIFO, priorities)
are part of the model. -/
structure SamplePath where
  /-- Arrival instant of customer `n`. -/
  a : ℕ → ℝ
  /-- Departure instant of customer `n`. No ordering is assumed:
  customers may overtake. -/
  d : ℕ → ℝ
  /-- Time starts at zero. -/
  a_nonneg : ∀ n, 0 ≤ a n
  /-- No customer departs before arriving. -/
  a_le_d : ∀ n, a n ≤ d n
  /-- Customers are indexed in arrival order. -/
  a_mono : Monotone a

/-!
## Counting-function asymptotics

The one analytic lemma both counts need, proved once: if `f n / n → τ`
and the count `c : ℝ → ℕ` satisfies two one-sided bounds — `t ≤ f (c t)`
and `f k ≤ t` below the count — then `c t / t → 1/τ`. Monotonicity of
`f` is **not** required: this is the inversion the overtaking case
needs.
-/

/-- A counting function dominated below through `f` diverges: whenever
`t ≤ f (c t)`, the count must leave every finite prefix, because `f` is
bounded on it. -/
theorem count_tendsto_atTop {f : ℕ → ℝ} {c : ℝ → ℕ}
    (hub : ∀ t, t ≤ f (c t)) : Tendsto c atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ k < M, f k < T := by
    refine ⟨1 + ∑ j ∈ Finset.range M, |f j|, fun k hk => ?_⟩
    have h1 : f k ≤ |f k| := le_abs_self _
    have h2 : |f k| ≤ ∑ j ∈ Finset.range M, |f j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (f j))
        (Finset.mem_range.mpr hk)
    linarith
  filter_upwards [Filter.eventually_ge_atTop T] with t ht
  by_contra hcM
  push Not at hcM
  exact absurd (hub t) (not_le.mpr (lt_of_lt_of_le (hT _ hcM) ht))

/-- `(n - 1) / n → 1` (natural subtraction, cast to `ℝ`). Mathlib's
`tendsto_natCast_div_add_atTop` at `x = -1` inverted: upstream gives
`n / (n + x)`, so the reciprocal and the `ℕ`-subtraction cast are what this
statement adds. -/
theorem tendsto_pred_div :
    Tendsto (fun m : ℕ => ((m - 1 : ℕ) : ℝ) / m) atTop (nhds 1) := by
  have h := (tendsto_natCast_div_add_atTop (-1 : ℝ)).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  rw [inv_div, Nat.cast_sub hm, Nat.cast_one, ← sub_eq_add_neg]

/-- `(n + 1) / n → 1` (cast to `ℝ`). Mathlib's
`tendsto_natCast_div_add_atTop` at `x = 1` inverted; the reciprocal and the
`ℕ`-cast of the numerator are the difference. -/
theorem tendsto_succ_div :
    Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ) / m) atTop (nhds 1) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr fun m => ?_
  rw [inv_div, Nat.cast_add, Nat.cast_one]

/-- **Count inversion, no monotonicity.** If `f n / n → τ > 0` and the
count `c` satisfies the two one-sided bounds — `t` never exceeds `f` at
the count, and `f` below the count never exceeds `t` — then
`c t / t → 1/τ`. Proof: squeeze `t / c t` between `f (c t - 1) / c t`
and `f (c t) / c t`, both converging to `τ` by composition, then
invert. -/
theorem count_div_tendsto {f : ℕ → ℝ} {c : ℝ → ℕ} {τ : ℝ} (hτ : 0 < τ)
    (hf : Tendsto (fun n => f n / n) atTop (nhds τ))
    (hub : ∀ t, t ≤ f (c t)) (hlb : ∀ t, ∀ k < c t, f k ≤ t) :
    Tendsto (fun t => (c t : ℝ) / t) atTop (nhds τ⁻¹) := by
  have hc_top : Tendsto c atTop atTop := count_tendsto_atTop hub
  have hupper : Tendsto (fun t => f (c t) / (c t : ℝ)) atTop (nhds τ) :=
    hf.comp hc_top
  have hg : Tendsto (fun m : ℕ => f (m - 1) / m) atTop (nhds τ) := by
    have h1 : Tendsto (fun m : ℕ => f (m - 1) / ((m - 1 : ℕ) : ℝ))
        atTop (nhds τ) := hf.comp (tendsto_sub_atTop_nat 1)
    have h2 := h1.mul tendsto_pred_div
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with m hm
    rw [div_mul_div_cancel₀
      (Nat.cast_ne_zero.mpr (by omega : (m - 1 : ℕ) ≠ 0))]
  have hlower : Tendsto (fun t => f (c t - 1) / (c t : ℝ)) atTop
      (nhds τ) := hg.comp hc_top
  have hmid : Tendsto (fun t => t / (c t : ℝ)) atTop (nhds τ) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
    · filter_upwards [hc_top.eventually_ge_atTop 1] with t hct
      exact div_le_div_of_nonneg_right (hlb t _ (by omega))
        (Nat.cast_nonneg _)
    · exact Filter.Eventually.of_forall fun t =>
        div_le_div_of_nonneg_right (hub t) (Nat.cast_nonneg _)
  have hinv := hmid.inv₀ (ne_of_gt hτ)
  exact hinv.congr fun t => inv_div _ _

/-- **Cesàro composition with a count.** If the partial-sum averages
converge, `S n / n → L`, and the count grows linearly, `c t / t → ρ`
with `c → ∞`, then `S (c t) / t → L·ρ`. The envelope step both sandwich
sides of `little` and `brumelle` share: split off `S (c t) / c t` and
multiply the limits. -/
theorem count_comp_div_tendsto {S : ℕ → ℝ} {c : ℝ → ℕ} {L ρ : ℝ}
    (hS : Tendsto (fun n => S n / n) atTop (nhds L))
    (hc : Tendsto (fun t => (c t : ℝ) / t) atTop (nhds ρ))
    (hc_top : Tendsto c atTop atTop) :
    Tendsto (fun t => S (c t) / t) atTop (nhds (L * ρ)) := by
  have h1 : Tendsto (fun t => S (c t) / (c t : ℝ)) atTop (nhds L) :=
    hS.comp hc_top
  have h2 := h1.mul hc
  refine h2.congr' ?_
  filter_upwards [hc_top.eventually_ge_atTop 1] with t hct
  rw [div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr (by omega : c t ≠ 0))]

namespace SamplePath

variable (P : SamplePath)

/-- Sojourn (time in system) of customer `n`. -/
def W (n : ℕ) : ℝ := P.d n - P.a n

/-- Sojourns are nonnegative. -/
theorem W_nonneg (n : ℕ) : 0 ≤ P.W n := sub_nonneg.mpr (P.a_le_d n)

/-- Cumulative sojourn of the first `n` customers. -/
def sojournSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, P.W k

/-- One customer at a time: the sojourn sum steps by `W`. -/
theorem sojournSum_succ_sub (n : ℕ) :
    P.sojournSum (n + 1) - P.sojournSum n = P.W n := by
  change (∑ k ∈ Finset.range (n + 1), P.W k)
      - ∑ k ∈ Finset.range n, P.W k = P.W n
  rw [Finset.sum_range_succ]
  ring

/-- Time spent in the system before `t` by customer `n`: the length of
`[a n, d n) ∩ [0, t)` for `t ≥ 0`, in min form. -/
def timeIn (t : ℝ) (n : ℕ) : ℝ := min (P.d n) t - min (P.a n) t

/-- Time in system before `t` is nonnegative. -/
theorem timeIn_nonneg (t : ℝ) (n : ℕ) : 0 ≤ P.timeIn t n :=
  sub_nonneg.mpr (min_le_min (P.a_le_d n) le_rfl)

/-- Time in system before `t` never exceeds the full sojourn. -/
theorem timeIn_le_W (t : ℝ) (n : ℕ) : P.timeIn t n ≤ P.W n := by
  change min (P.d n) t - min (P.a n) t ≤ P.d n - P.a n
  rcases le_total (P.a n) t with h | h
  · rw [min_eq_left h]
    exact sub_le_sub_right (min_le_left _ _) _
  · rw [min_eq_right h, min_eq_right (h.trans (P.a_le_d n)), sub_self]
    exact sub_nonneg.mpr (P.a_le_d n)

/-- A customer departed by `t` has spent its full sojourn. -/
theorem timeIn_eq_W_of_d_le {t : ℝ} {n : ℕ} (h : P.d n ≤ t) :
    P.timeIn t n = P.W n := by
  change min (P.d n) t - min (P.a n) t = P.d n - P.a n
  rw [min_eq_left h, min_eq_left ((P.a_le_d n).trans h)]

/-- A customer not yet arrived by `t` has spent nothing. -/
theorem timeIn_eq_zero_of_le_a {t : ℝ} {n : ℕ} (h : t ≤ P.a n) :
    P.timeIn t n = 0 := by
  change min (P.d n) t - min (P.a n) t = 0
  rw [min_eq_right (h.trans (P.a_le_d n)), min_eq_right h, sub_self]

/-- The index of the first arrival at or after `t` — with ordered
arrivals, the number of customers arrived strictly before `t` (junk `0`
when no arrival ever reaches `t`, per the totality convention; the
theorems supply nonemptiness). -/
noncomputable def arrivals (t : ℝ) : ℕ := sInf {n | t ≤ P.a n}

/-- The longest initial segment fully departed by `t`. With overtaking,
customers beyond the prefix may also have departed — the prefix is what
the lower sandwich needs, and it needs no order on departures. -/
noncomputable def departedPrefix (t : ℝ) : ℕ := sInf {n | t < P.d n}

/-- Below the arrival count, customers have arrived. -/
theorem a_lt_of_lt_arrivals {t : ℝ} {k : ℕ} (hk : k < P.arrivals t) :
    P.a k < t := by
  by_contra h
  have hmem : k ∈ {n | t ≤ P.a n} := not_lt.mp h
  exact absurd (Nat.sInf_le hmem) (not_le.mpr hk)

/-- At or beyond the arrival count, customers have not arrived (ordered
arrivals). -/
theorem le_a_of_arrivals_le {t : ℝ} (hne : {n | t ≤ P.a n}.Nonempty)
    {k : ℕ} (hk : P.arrivals t ≤ k) : t ≤ P.a k :=
  le_trans (Nat.sInf_mem hne) (P.a_mono hk)

/-- Below the departed prefix, customers have departed — no order on
departures needed. -/
theorem d_le_of_lt_departedPrefix {t : ℝ} {k : ℕ}
    (hk : k < P.departedPrefix t) : P.d k ≤ t := by
  by_contra h
  have hmem : k ∈ {n | t < P.d n} := not_le.mp h
  exact absurd (Nat.sInf_le hmem) (not_le.mpr hk)

/-- The customer at the departed prefix has not departed. -/
theorem lt_d_departedPrefix {t : ℝ} (hne : {n | t < P.d n}.Nonempty) :
    t < P.d (P.departedPrefix t) := Nat.sInf_mem hne

/-- Cumulative occupancy before `t`: the area under the number-in-system
step function, as the finite sum of per-customer time in system over the
arrived prefix — customers at or beyond `arrivals t` contribute zero
(`timeIn_eq_zero_of_le_a`). -/
noncomputable def area (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.arrivals t), P.timeIn t k

/-- Upper sandwich: occupancy is at most the total sojourn of the
arrived. -/
theorem area_le_sojournSum (t : ℝ) :
    P.area t ≤ P.sojournSum (P.arrivals t) :=
  Finset.sum_le_sum fun k _ => P.timeIn_le_W t k

/-- Lower sandwich: the fully-departed prefix's total sojourn is already
contained in the occupancy. -/
theorem sojournSum_departedPrefix_le {t : ℝ}
    (hne : {n | t ≤ P.a n}.Nonempty) :
    P.sojournSum (P.departedPrefix t) ≤ P.area t := by
  have h1 : P.sojournSum (P.departedPrefix t)
      = ∑ k ∈ Finset.range (P.departedPrefix t), P.timeIn t k :=
    Finset.sum_congr rfl fun k hk =>
      (P.timeIn_eq_W_of_d_le
        (P.d_le_of_lt_departedPrefix (Finset.mem_range.mp hk))).symm
  rw [h1]
  change _ ≤ ∑ k ∈ Finset.range (P.arrivals t), P.timeIn t k
  rcases le_total (P.departedPrefix t) (P.arrivals t) with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset.mpr fun x hx =>
        Finset.mem_range.mpr (lt_of_lt_of_le hx h))
      fun k _ _ => P.timeIn_nonneg t k
  · refine le_of_eq (Finset.sum_subset
      (Finset.range_subset.mpr fun x hx =>
        Finset.mem_range.mpr (lt_of_lt_of_le hx h))
      fun k _ hk' => ?_).symm
    exact P.timeIn_eq_zero_of_le_a (P.le_a_of_arrivals_le hne
      (not_lt.mp fun hlt => hk' (Finset.mem_range.mpr hlt)))

/-- **The Cesàro tail bound**: once the sojourn averages converge, single
sojourns are `o(n)` — `W n / n → 0`. -/
theorem tendsto_W_div {Wbar : ℝ}
    (hH2 : Tendsto (fun n => P.sojournSum n / n) atTop (nhds Wbar)) :
    Tendsto (fun n => P.W n / n) atTop (nhds 0) := by
  have hsucc : Tendsto (fun n : ℕ => P.sojournSum (n + 1) / n) atTop
      (nhds Wbar) := by
    have h1 : Tendsto
        (fun n : ℕ => P.sojournSum (n + 1) / ((n + 1 : ℕ) : ℝ))
        atTop (nhds Wbar) := hH2.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.mul tendsto_succ_div
    rw [mul_one] at h2
    exact h2.congr fun n => by
      rw [div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr n.succ_ne_zero)]
  have h3 := hsucc.sub hH2
  rw [sub_self] at h3
  refine h3.congr fun n => ?_
  rw [← sub_div, P.sojournSum_succ_sub n]

/-- **The departure rate equals the arrival rate**: sojourns are `o(n)`
by the Cesàro tail, so departures cannot drift — `d n / n → τ`. -/
theorem tendsto_d_div {τ Wbar : ℝ}
    (hH1 : Tendsto (fun n => P.a n / n) atTop (nhds τ))
    (hH2 : Tendsto (fun n => P.sojournSum n / n) atTop (nhds Wbar)) :
    Tendsto (fun n => P.d n / n) atTop (nhds τ) := by
  have h := hH1.add (P.tendsto_W_div hH2)
  rw [add_zero] at h
  refine h.congr fun n => ?_
  change P.a n / n + (P.d n - P.a n) / n = P.d n / n
  ring

/-- H1 forces the arrival instants to infinity. -/
theorem tendsto_a_atTop {τ : ℝ} (hτ : 0 < τ)
    (hH1 : Tendsto (fun n => P.a n / n) atTop (nhds τ)) :
    Tendsto P.a atTop atTop := by
  have hev : ∀ᶠ n : ℕ in atTop, τ / 2 ≤ P.a n / n :=
    hH1.eventually (eventually_ge_nhds (by linarith))
  have hgrow : Tendsto (fun n : ℕ => τ / 2 * n) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' _ ?_ hgrow
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with n h1 hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  calc τ / 2 * n ≤ P.a n / n * n :=
        mul_le_mul_of_nonneg_right h1 hn0.le
    _ = P.a n := div_mul_cancel₀ _ (ne_of_gt hn0)

/-- **The shared count asymptotics.** Under H1 and H2 the sandwich's whole
preamble holds at once: every arrival set `{n | t ≤ a n}` is nonempty (so the
lower sandwich applies), both counting functions grow at the arrival rate
(`arrivals t / t → 1/τ`, `departedPrefix t / t → 1/τ`), and both diverge. The
departed side runs through `tendsto_d_div`, which is why H2 is needed here and
not only for the sojourn mean. `little` and `brumelle` consume this lemma and
differ only in which Cesàro mean they feed the envelope. -/
theorem count_asymptotics {τ Wbar : ℝ} (hτ : 0 < τ)
    (hH1 : Tendsto (fun n => P.a n / n) atTop (nhds τ))
    (hH2 : Tendsto (fun n => P.sojournSum n / n) atTop (nhds Wbar)) :
    (∀ t : ℝ, {n | t ≤ P.a n}.Nonempty) ∧
      Tendsto (fun t => (P.arrivals t : ℝ) / t) atTop (nhds τ⁻¹) ∧
      Tendsto (fun t => (P.departedPrefix t : ℝ) / t) atTop (nhds τ⁻¹) ∧
      Tendsto P.arrivals atTop atTop ∧
      Tendsto P.departedPrefix atTop atTop := by
  have ha_top : Tendsto P.a atTop atTop := P.tendsto_a_atTop hτ hH1
  have hd_top : Tendsto P.d atTop atTop :=
    tendsto_atTop_mono P.a_le_d ha_top
  have hAne : ∀ t : ℝ, {n | t ≤ P.a n}.Nonempty := fun t =>
    (ha_top.eventually_ge_atTop t).exists
  have hBne : ∀ t : ℝ, {n | t < P.d n}.Nonempty := fun t =>
    (hd_top.eventually_gt_atTop t).exists
  refine ⟨hAne, ?_, ?_, ?_, ?_⟩
  · exact count_div_tendsto hτ hH1 (fun t => Nat.sInf_mem (hAne t))
      (fun t _k hk => (P.a_lt_of_lt_arrivals hk).le)
  · exact count_div_tendsto hτ (P.tendsto_d_div hH1 hH2)
      (fun t => (P.lt_d_departedPrefix (hBne t)).le)
      (fun t _k hk => P.d_le_of_lt_departedPrefix hk)
  · exact count_tendsto_atTop (fun t => Nat.sInf_mem (hAne t))
  · exact count_tendsto_atTop (fun t => (P.lt_d_departedPrefix (hBne t)).le)

/-- **Little's law, deterministic sample-path form (Stidham).** If the
arrival instants have rate `1/τ` (H1: `a n / n → τ`, `τ > 0`) and the
sojourns have a Cesàro mean (H2: `(∑_{k<n} W k)/n → Wbar`), then the
long-run time-average number in system exists and equals `λ·Wbar` with
`λ = 1/τ`: `area t / t → Wbar/τ`. One deterministic trace, two rate
hypotheses — no distributions, no independence, no ergodicity, and no
order on departures (overtaking allowed). Identifying these time
averages with stationary quantities (as `MM1.lean` does definitionally)
remains an ergodic hypothesis, stated there. -/
theorem little {τ Wbar : ℝ} (hτ : 0 < τ)
    (hH1 : Tendsto (fun n => P.a n / n) atTop (nhds τ))
    (hH2 : Tendsto (fun n => P.sojournSum n / n) atTop (nhds Wbar)) :
    Tendsto (fun t => P.area t / t) atTop (nhds (Wbar / τ)) := by
  obtain ⟨hAne, hA, hB, hA_top, hB_top⟩ := P.count_asymptotics hτ hH1 hH2
  have hUenv := count_comp_div_tendsto hH2 hA hA_top
  have hLenv := count_comp_div_tendsto hH2 hB hB_top
  have hmain : Tendsto (fun t => P.area t / t) atTop
      (nhds (Wbar * τ⁻¹)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLenv hUenv ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      exact div_le_div_of_nonneg_right
        (P.sojournSum_departedPrefix_le (hAne t)) ht0.le
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      exact div_le_div_of_nonneg_right (P.area_le_sojournSum t) ht0.le
  rw [div_eq_mul_inv]
  exact hmain

/-!
## Brumelle's formula

The weighted generalization `H = λG`: replace each customer's unit
contribution by a nonnegative per-customer rate. Definitions,
sandwich, and theorem mirror the unweighted ones above, and the
unit-weight instance returns `little`.
-/

/-- Cumulative value of the first `n` customers under the per-customer
weight `g`: customer `k` is worth `g k · W k` — value accrued at the
constant rate `g k` for exactly its sojourn. A finite real sum, total,
with no division; the weights are unrestricted here, and nonnegativity
enters only where the sandwich lemmas state it. -/
def valueSum (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, g k * P.W k

/-- Cumulative value in system before `t`: each arrived customer
contributes its time in system so far, scaled by its weight — the area
under the value-in-system step function, mirroring `area` (customers at
or beyond `arrivals t` would contribute zero). -/
noncomputable def valueArea (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.arrivals t), g k * P.timeIn t k

/-- At unit weight, cumulative value is cumulative sojourn. -/
theorem valueSum_one (n : ℕ) :
    P.valueSum (fun _ => 1) n = P.sojournSum n := by
  simp [valueSum, sojournSum]

/-- At unit weight, value in system is occupancy. -/
theorem valueArea_one (t : ℝ) :
    P.valueArea (fun _ => 1) t = P.area t := by
  simp [valueArea, area]

/-- Weighted upper sandwich: value in system is at most the total value
of the arrived. -/
theorem valueArea_le_valueSum {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (t : ℝ) :
    P.valueArea g t ≤ P.valueSum g (P.arrivals t) :=
  Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (P.timeIn_le_W t k) (hg k)

/-- Weighted lower sandwich: the fully-departed prefix's total value is
already contained in the value in system. -/
theorem valueSum_departedPrefix_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    {t : ℝ} (hne : {n | t ≤ P.a n}.Nonempty) :
    P.valueSum g (P.departedPrefix t) ≤ P.valueArea g t := by
  have h1 : P.valueSum g (P.departedPrefix t)
      = ∑ k ∈ Finset.range (P.departedPrefix t), g k * P.timeIn t k :=
    Finset.sum_congr rfl fun k hk => by
      rw [P.timeIn_eq_W_of_d_le
        (P.d_le_of_lt_departedPrefix (Finset.mem_range.mp hk))]
  rw [h1]
  change _ ≤ ∑ k ∈ Finset.range (P.arrivals t), g k * P.timeIn t k
  rcases le_total (P.departedPrefix t) (P.arrivals t) with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset.mpr fun x hx =>
        Finset.mem_range.mpr (lt_of_lt_of_le hx h))
      fun k _ _ => mul_nonneg (hg k) (P.timeIn_nonneg t k)
  · refine le_of_eq (Finset.sum_subset
      (Finset.range_subset.mpr fun x hx =>
        Finset.mem_range.mpr (lt_of_lt_of_le hx h))
      fun k _ hk' => ?_).symm
    rw [P.timeIn_eq_zero_of_le_a (P.le_a_of_arrivals_le hne
      (not_lt.mp fun hlt => hk' (Finset.mem_range.mpr hlt))), mul_zero]

/-- **Brumelle's formula, deterministic sample-path form (`H = λG`).**
Give customer `n` a nonnegative weight `g n`, so it accrues value at the
constant rate `g n` while in system, `G n = g n·W n` in total. Under
Little's hypotheses (H1: `a n / n → τ`, `τ > 0`; H2: Cesàro sojourn mean
`Wbar`) plus the value analogue of H2 (H3: `(∑_{k<n} g k·W k)/n → Gbar`), the
long-run time-average value in system exists and equals `λ·Gbar` with
`λ = 1/τ`: `valueArea g t / t → Gbar/τ`. Same trace, same counts, same
sandwich — no distributions, no order on departures. H2 is still needed
on its own: it drives the departure rate (`tendsto_d_div`) behind the
lower sandwich, which H3 alone does not supply. This is the
constant-rate-per-customer case of `H = λG`; time-varying accrual
profiles are not formalized. `little` is the unit-weight instance
(`little_of_brumelle`). -/
theorem brumelle {g : ℕ → ℝ} {τ Wbar Gbar : ℝ} (hτ : 0 < τ)
    (hg : ∀ n, 0 ≤ g n)
    (hH1 : Tendsto (fun n => P.a n / n) atTop (nhds τ))
    (hH2 : Tendsto (fun n => P.sojournSum n / n) atTop (nhds Wbar))
    (hH3 : Tendsto (fun n => P.valueSum g n / n) atTop (nhds Gbar)) :
    Tendsto (fun t => P.valueArea g t / t) atTop (nhds (Gbar / τ)) := by
  obtain ⟨hAne, hA, hB, hA_top, hB_top⟩ := P.count_asymptotics hτ hH1 hH2
  have hUenv := count_comp_div_tendsto hH3 hA hA_top
  have hLenv := count_comp_div_tendsto hH3 hB hB_top
  have hmain : Tendsto (fun t => P.valueArea g t / t) atTop
      (nhds (Gbar * τ⁻¹)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLenv hUenv ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      exact div_le_div_of_nonneg_right
        (P.valueSum_departedPrefix_le hg (hAne t)) ht0.le
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      exact div_le_div_of_nonneg_right (P.valueArea_le_valueSum hg t) ht0.le
  rw [div_eq_mul_inv]
  exact hmain

/-- **`L = λW` is `H = λG` at unit weight** — the specialization bridge
that keeps the generalization honest: with `g ≡ 1` the per-customer
value is the sojourn time (`valueSum_one`), the value in system is the
occupancy (`valueArea_one`), and `brumelle` returns exactly the
conclusion of `little`, from the same two hypotheses. -/
theorem little_of_brumelle {τ Wbar : ℝ} (hτ : 0 < τ)
    (hH1 : Tendsto (fun n => P.a n / n) atTop (nhds τ))
    (hH2 : Tendsto (fun n => P.sojournSum n / n) atTop (nhds Wbar)) :
    Tendsto (fun t => P.area t / t) atTop (nhds (Wbar / τ)) := by
  have h := P.brumelle (g := fun _ => 1) hτ (fun _ => zero_le_one) hH1
    hH2 (by simpa only [P.valueSum_one] using hH2)
  simpa only [P.valueArea_one] using h

/-- Non-vacuity regression: on the unit-spaced path `aₙ = n`,
`dₙ = n + 1` (every sojourn `1`) with constant weight `2`, the first
three customers carry cumulative value `2·3 = 6`. -/
theorem valueSum_unitPath_weight_two :
    SamplePath.valueSum
      { a := fun n => (n : ℝ), d := fun n => (n : ℝ) + 1,
        a_nonneg := fun n => Nat.cast_nonneg n,
        a_le_d := fun _ => by linarith,
        a_mono := fun _ _ h => Nat.cast_le.mpr h }
      (fun _ => 2) 3 = 6 := by
  change ∑ k ∈ Finset.range 3, (2 : ℝ) * (((k : ℝ) + 1) - (k : ℝ)) = 6
  norm_num [Finset.sum_range_succ]

end SamplePath

end Overload
