import Mathlib
import Overload.Operator
import Overload.Bistability

/-!
# Bursts vs. basins: the trigger-size arithmetic, and jitter as trigger-avoidance

The deterministic core of the trigger story: a synchronized cohort of `B`
requests released over a window `w` adds a spike `B/w` to the baseline demand `Λ₀`,
and what matters is only which side of the middle fixed point (the
separatrix) the spiked demand `Λ₀ + B/w` lands on.

* `jitter_window_avoids` — **jitter is trigger-avoidance**: any window at
  least `B/(z − Λ₀)` keeps the spike at or below the separatrix `z`. This is
  the sizing inequality behind "add jitter": spreading the cohort does not
  reduce its demand, it reduces its *rate*, and the required spread is
  computable from the basin gap.
* `ClosedLoop.burst_safe` — the safe side, on the loop: a spiked demand at
  or below a fixed point never crosses it under iteration
  (`iterate_le_of_le_fixedPt`).
* `ClosedLoop.burst_tips` — the tipping side: a spiked demand that is
  postfixed (`x ≤ F x`) ratchets upward under iteration — the storm feeds
  itself (`le_iterate_of_postfixed`, which this theorem gives its named
  consumer).
* `ClosedLoop.burst_crosses` / `stepLoop_burst_crosses` — the crossing side,
  sized: a spike that closes the gap to the threshold and is postfixed there
  certifies a congested equilibrium at the threshold. On the stylized loop
  the postfixed hypothesis becomes arithmetic — reach capacity, stay inside
  the demand envelope — and the minimum burst *rate* `C − Λ₀` is the same
  basin gap that sizes the minimum jitter *window* in
  `jitter_window_avoids`.

What is deliberately **not** claimed: nothing stochastic (no cohort-arrival
distribution, no synchronization dynamics, no exit times — the omitted
list's territory). The return-time side of a burst — the backlog draining
after the spike — is the continuous drain bound in `Calculus.lean`
(`fluid_drain_clears`); no theorem links it to the demand iterates here,
and the bridge between the two readings is a modeling step, not a lemma.
-/

namespace Overload

/-- **Jitter is trigger-avoidance.** A cohort `B` spread over any window
`w ≥ B/(z − Λ₀)` keeps the spiked demand `Λ₀ + B/w` at or below the
threshold `z` — the minimum jitter window is computable from the basin gap
`z − Λ₀`. -/
theorem jitter_window_avoids {B Λ₀ z w : ℝ} (hgap : Λ₀ < z)
    (hw : B / (z - Λ₀) ≤ w) (hw0 : 0 < w) : Λ₀ + B / w ≤ z := by
  have hgap0 : 0 < z - Λ₀ := sub_pos.mpr hgap
  have h1 : B ≤ w * (z - Λ₀) := (div_le_iff₀ hgap0).mp hw
  have h2 : B / w ≤ z - Λ₀ := (div_le_iff₀ hw0).mpr (by linarith)
  linarith

/-- **The safe side of the trigger threshold.** A burst whose spiked demand
`Λ₀ + B/w` lands at or below a fixed point `z` of the loop never crosses it:
every iterate of the demand map stays at or below `z`, so the congested
branch is unreachable from this burst. -/
theorem ClosedLoop.burst_safe (L : ClosedLoop) {z Λ₀ B w : ℝ}
    (hz : z ∈ Set.Icc 0 (L.lam * L.Amax)) (hfz : Function.IsFixedPt L.F z)
    (hΛ₀ : 0 ≤ Λ₀) (hB : 0 ≤ B) (hw : 0 < w)
    (htrig : Λ₀ + B / w ≤ z) (n : ℕ) : L.F^[n] (Λ₀ + B / w) ≤ z :=
  iterate_le_of_le_fixedPt L.F_monotoneOn_Icc L.F_mapsTo hz hfz
    ⟨by positivity, htrig.trans hz.2⟩ htrig n

/-- **The tipping side.** A spiked demand that is postfixed (`x ≤ F x` —
attempt inflow at the spike already sustains it) ratchets upward under
iteration: each step of the demand map is at least the last. Past the
separatrix, the storm feeds itself. -/
theorem ClosedLoop.burst_tips (L : ClosedLoop) {Λ₀ B w : ℝ}
    (h0 : 0 ≤ Λ₀ + B / w) (hpost : Λ₀ + B / w ≤ L.F (Λ₀ + B / w)) (n : ℕ) :
    L.F^[n] (Λ₀ + B / w) ≤ L.F^[n + 1] (Λ₀ + B / w) :=
  le_iterate_of_postfixed L.F_monotoneOn_Icc L.F_mapsTo
    ⟨h0, hpost.trans (L.F_le h0)⟩ hpost n

/-- **The crossing side, sized.** A spike `B/w` that closes the gap from the
baseline `Λ₀` to the threshold `Θ` and is postfixed there (`x ≤ F x` at the
spiked demand `x = Λ₀ + B/w`) certifies a congested equilibrium at `Θ`:
Knaster–Tarski above the spike returns a fixed point at or above it, hence at
or above `Θ`. The same basin gap that sizes the safe window in
`jitter_window_avoids` sizes the crossing burst here, from the other side.
Read it with `ClosedLoop.burst_tips`, which turns the same postfixedness into
the upward ratchet under iteration. -/
theorem ClosedLoop.burst_crosses (L : ClosedLoop) {Λ₀ B w Θ : ℝ}
    (hΛ₀ : 0 ≤ Λ₀) (hw : 0 < w) (hB : 0 ≤ B) (htrig : Θ - Λ₀ ≤ B / w)
    (hpost : Λ₀ + B / w ≤ L.F (Λ₀ + B / w)) : L.CongestedEq Θ := by
  have hx0 : 0 ≤ Λ₀ + B / w := by positivity
  have hxM : Λ₀ + B / w ≤ L.lam * L.Amax := hpost.trans (L.F_le hx0)
  obtain ⟨z, hzmem, hzfix⟩ := exists_fixedPt_ge (F := L.F) (a := 0)
    (b := L.lam * L.Amax) L.F_monotoneOn_Icc L.F_mapsTo ⟨hx0, hxM⟩ hpost
  exact ⟨z, hx0.trans hzmem.1, hzfix, by linarith [hzmem.1]⟩

/-- **The crossing burst, in arithmetic.** On the stylized loop the postfixed
hypothesis of `ClosedLoop.burst_crosses` is two inequalities on numbers: the
spike reaches capacity (`hreach`, whose readable form is `C − Λ₀ ≤ B/w` — the
minimum burst *rate* is the basin gap) and stays inside the demand envelope
(`hcap`). Then a congested equilibrium exists at `C`. This mirrors
`jitter_window_avoids`, which sizes the minimum jitter *window*
`w ≥ B/(z − Λ₀)` off the same gap: one spreads the cohort until the added
rate falls below the gap, the other concentrates it until the rate clears it.

`hcap` is a hypothesis, not decoration: a spike above `lam·A` is outside the
loop's own demand envelope and the argument does not run there.

What this does not prove: anything in real time. This is monotone iteration
rather than a flow, and nothing here prices how long the crossing takes; that
a burst of that size is deliverable; or anything about synchronization, which
a mean-field model cannot see. -/
theorem stepLoop_burst_crosses {lam C A Λ₀ B w : ℝ} (hlam : 0 < lam)
    (hA : 1 ≤ A) (hΛ₀ : 0 ≤ Λ₀) (hw : 0 < w) (hB : 0 ≤ B)
    (hreach : C ≤ Λ₀ + B / w) (hcap : Λ₀ + B / w ≤ lam * A) :
    (stepLoop lam C A hlam.le hA).CongestedEq C := by
  refine (stepLoop lam C A hlam.le hA).burst_crosses hΛ₀ hw hB (by linarith) ?_
  rw [stepLoop_F_of_ge hlam.le hA hreach]
  exact hcap

/-- Numeric regression on the jitter inequality: a window of `3` holds a
cohort of `3` against a basin gap of `1`, the spike landing exactly on the
separatrix. Sufficiency only: nothing here proves a smaller window fails. -/
theorem jitter_window_avoids_three : (1 : ℝ) + 3 / 3 ≤ 2 :=
  jitter_window_avoids (by norm_num) (by norm_num) (by norm_num)

/-- Numeric regression on the safe side: `stepLoop 1 2 3` has the healthy
fixed point `1`; a burst of `1` over a window of `4` on baseline `1/2`
spikes demand to `3/4 ≤ 1`, and no number of iterations crosses `1`. -/
theorem burst_safe_stepLoop_five :
    (stepLoop 1 2 3 (by norm_num) (by norm_num)).F^[5] (1/2 + 1/4) ≤ 1 := by
  have hfz : Function.IsFixedPt (stepLoop 1 2 3 (by norm_num)
      (by norm_num)).F 1 := by
    change (1 : ℝ) * (1 + stepKernel 2 1 * (3 - 1)) = 1
    rw [stepKernel_of_lt (by norm_num)]
    norm_num
  have h := (stepLoop 1 2 3 (by norm_num) (by norm_num)).burst_safe
    (z := 1) (Λ₀ := 1/2) (B := 1) (w := 4)
    ⟨by norm_num, by change (1 : ℝ) ≤ 1 * 3; norm_num⟩ hfz (by norm_num)
    (by norm_num)
    (by norm_num) (by norm_num) 5
  simpa using h

/-- Numeric regression on the crossing side: on `stepLoop 1 2 3` a cohort of
`6` released over a window of `4` lifts baseline `1/2` to exactly capacity
`2`, inside the demand envelope `1·3`, so a congested equilibrium exists at
`2`. -/
theorem burst_crosses_stepLoop_two :
    (stepLoop 1 2 3 (by norm_num) (by norm_num)).CongestedEq 2 :=
  stepLoop_burst_crosses (Λ₀ := 1/2) (B := 6) (w := 4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Numeric regression on the ratchet, at the same crossing burst: the spike
lands on capacity `2`, where the demand map already exceeds it, so the spike is
postfixed and the iterates climb. Stated at the third step. -/
theorem burst_tips_stepLoop_two :
    (stepLoop 1 2 3 (by norm_num) (by norm_num)).F^[3] (1 / 2 + 6 / 4)
      ≤ (stepLoop 1 2 3 (by norm_num) (by norm_num)).F^[3 + 1] (1 / 2 + 6 / 4) :=
  (stepLoop 1 2 3 (by norm_num) (by norm_num)).burst_tips (by norm_num)
    (by
      change (1 / 2 + 6 / 4 : ℝ) ≤ 1 * (1 + stepKernel 2 (1 / 2 + 6 / 4) * (3 - 1))
      rw [stepKernel_of_ge (by norm_num)]
      norm_num) 3

end Overload
