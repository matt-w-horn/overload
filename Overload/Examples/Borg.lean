import Mathlib
import Overload.Bistability
import Overload.Scheme
import Overload.Conservation
import Overload.Plateau
import Overload.Priority

/-!
# Example: a Borg-style cluster scheduler, and multi-tenant fairness

A cluster scheduler in the style of Borg (Verma et al., "Large-scale cluster
management at Google with Borg", EuroSys 2015 — public paper): tenants submit
jobs into **priority bands** (production above batch above best-effort), a
higher band may **preempt** a lower band's tasks, preempted tasks are
**rescheduled** — a retry performed by the architecture — and admission is
controlled by **quota** denominated in resources at a priority. Task startup
is expensive (Verma et al. report a median around 25 s), so an eviction destroys
real invested work.

This file is the one place in the library that discusses **multi-tenant
fairness** explicitly, because Borg's public design is the canonical instance
of the open problem — *who gets the retries when the budget
binds?* — and the theorems answer its two halves:

* **Without cooperation from the resource** (the scheduler cannot or will not
  discriminate): per-band reschedule budgets alone give every band an explicit
  goodput-share floor (`borg_band_floor`). Fairness from budgets, with a
  blind resource.
* **With intent labels at the boundary**: strict priority plus work
  conservation gives the production band full isolation — its allocation is
  `min(demand, C)` *whatever any lower band's retry storm does*
  (`borg_prod_immune`) — while no capacity is ever stranded
  (`borg_no_stranding`, `borg_batch_borrows`): lower bands borrow every idle
  unit. The classic utilization objection to strict priority, answered as a
  theorem. And the allocation composes with the equilibrium theory: each
  band runs as its own closed loop over its allocated capacity
  (`borg_batch_over_residual` — a clamp certificate at batch's residual 40).

The overload story, mapped mechanism by mechanism:

* **Rescheduling is retry with a load-coupled kernel**: placement failure
  probability rises as cells fill. A batch band at 30 placements/s against a
  100 placements/s scheduler, with rescheduling amplification 4 under
  saturation, is bistable (`borg_batch_bistable`) — an eviction storm can be
  self-sustaining after its trigger ends.
* **Eviction destroys startup investment — the waste channel**: a preempted
  task's ~25 s of startup work is bottleneck work that produced no goodput.
  `borg_waste_caps_goodput` prices a 25% eviction-waste fraction, and
  `borg_cliff_needs_waste` instantiates the plateau converse: any observed
  goodput cliff under overload is evidence of a positive waste fraction —
  with zero waste the plateau theorem forbids it.
* **Preemption cascades are stack composition**: an eviction at one band
  triggering re-placement at another composes multiplicatively. The composite
  is still one closed loop, and one product inequality certifies the whole
  cascade collapse-free (`borg_cascade_certified`) — for every failure
  kernel.
* **Quota is admission denominated in requests**: quota bounds *submissions*,
  but the scheduler serves *placement attempts*. Without a reschedule clamp,
  a fixed quota bounds nothing (`borg_quota_needs_clamp`); with a per-task
  replacement clamp it bounds attempt load exactly (`borg_quota_bound`).

Numbers are stylized illustrations of the public design (except the ~25 s
startup median, which is Verma et al.'s), chosen to make every certificate close
by `norm_num`. The claims are about the structure, not about Google's
production parameters.
-/

namespace Overload

/-!
## Priority at the boundary: isolation with no stranding
-/

/-- The two-band demand profile: production demands 60, batch demands `b`. -/
noncomputable def borgDemand (b : ℝ) : ℕ → ℝ := fun j => if j = 0 then 60 else b

/-- **Production is immune to the batch storm.** Whatever the batch band's
demand — including unbounded reschedule amplification — the production band's
allocation is exactly its demand: `min 60 100 = 60`. Priority enforced from
intent labels at the resource boundary makes the top band's outcome a function
of its own demand and capacity alone. -/
theorem borg_prod_immune (b : ℝ) : alloc (borgDemand b) 100 0 = 60 := by
  rw [top_class_isolation (by norm_num)]
  norm_num [borgDemand]

/-- The batch band's residual capacity: production takes 60 of 100, leaving
40 — the single source for the batch-side constant. -/
theorem borg_batch_residual : residual (borgDemand 80) 100 1 = 40 := by
  unfold residual borgDemand
  rw [Finset.sum_range_one]
  norm_num

/-- Batch borrows everything production leaves idle: with production at 60 of
100, batch demand 80 receives the full residual 40. -/
theorem borg_batch_borrows : alloc (borgDemand 80) 100 1 = 40 := by
  unfold alloc
  rw [borg_batch_residual]
  norm_num [borgDemand]

/-- **No stranding**: total allocation is `min(total demand, C)` — here the
full capacity 100 (production 60 + batch 40 of its demanded 80). Strict
priority wastes nothing; the utilization objection fails as arithmetic. -/
theorem borg_no_stranding :
    ∑ j ∈ Finset.range 2, alloc (borgDemand 80) 100 j = 100 := by
  rw [no_stranding (by norm_num)
    (fun j => by unfold borgDemand; split <;> norm_num) 2]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [borgDemand]

/-- **Per-class loop over allocated capacity** — the bridge between the
allocation arithmetic and the equilibrium machinery. Batch, offered 8 tasks/s
under a 4-placement reschedule clamp, runs as a closed loop over its
*residual* capacity `residual (borgDemand 80) 100 1 = 40`, and `8·4 = 32 <
40` certifies no congested equilibrium there: production's isolation
(`borg_prod_immune`) and batch's collapse-freedom compose, each phase theorem
instantiated at the class's own capacity. -/
theorem borg_batch_over_residual :
    ¬(cappedLoop 8 40 4 (by norm_num) (by norm_num)).CongestedEq
      (residual (borgDemand 80) 100 1) := by
  rw [borg_batch_residual]
  exact cappedLoop_no_congestedEq (by norm_num)

/-!
## Fairness from budgets alone, when the resource stays blind
-/

/-- **The per-band budget floor.** Production offers 3 placements/s, batch 9.
Under reschedule clamps of 2 (production) and 5 (batch), production's share of
total placement attempts is at least `3/51 ≈ 6%` — *whatever* batch's actual
amplification is below its clamp, and with no priority enforcement at the
scheduler at all. Budgets bound the arms race even when the resource cannot
tell tenants apart. -/
theorem borg_band_floor (A : Fin 2 → ℝ) (hA1 : ∀ j, 1 ≤ A j)
    (hA0 : A 0 ≤ 2) (hA1' : A 1 ≤ 5) :
    (3 : ℝ) / 51
      ≤ offeredAttempts ![3, 9] A 0 / (∑ j, offeredAttempts ![3, 9] A j) := by
  have h := budget_floor (lam := ![3, 9]) (A := A) (β := ![1, 4])
    (fun j => by fin_cases j <;> norm_num) hA1
    (Fin.forall_fin_two.mpr
      ⟨by simp only [Matrix.cons_val_zero]; linarith,
        by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; linarith⟩)
    0 (by norm_num)
  have hsum : (∑ j, (![3, 9] : Fin 2 → ℝ) j * (1 + (![1, 4] : Fin 2 → ℝ) j))
      = 51 := by
    rw [Fin.sum_univ_two]
    norm_num
  rw [hsum] at h
  simpa using h

/-!
## The batch band's bistability, and the waste that makes the cliff
-/

/-- **An eviction storm can be self-sustaining.** Batch at 30 placements/s
against a 100 placements/s scheduler, rescheduling amplification 4 under
saturated cells: the band `30 < 100 ≤ 120` is bistable. After a trigger (a
large job landing, a rack drain), the storm no longer needs the trigger. -/
theorem borg_batch_bistable :
    BistableOn (stepLoop 30 100 4 (by norm_num) (by norm_num)).F 0 (30 * 4) :=
  stepLoop_bistable (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Work accounting for a congested window: capacity 100 for one time unit;
70 useful, 25 destroyed as evicted-task startup investment, 5 idle. -/
noncomputable def borgAcct : Accounting where
  capacity := 100
  time := 1
  useful := 70
  wasted := 25
  idle := 5
  capacity_pos := by norm_num
  time_pos := by norm_num
  useful_nonneg := by norm_num
  wasted_nonneg := by norm_num
  idle_nonneg := by norm_num
  conserve := by norm_num

/-- **Eviction waste prices the cliff**: with 25% of scheduler work destroyed
as lost startup investment and 5% of capacity left idle, goodput (in work
units) is capped at 75% of capacity less the idle share — 70. Each point of
eviction waste is a point off the top, and each point of idle is another.
Disclosed: this accounting is fully specified, so the ceiling necessarily
lands on its own `useful` figure; the transferable content is the
decomposition `(1-w)·C - I/T`, not a bound the accounting did not already
contain. -/
theorem borg_waste_caps_goodput {G : ℝ}
    (huseful : G * borgAcct.time * 1 ≤ borgAcct.useful) :
    G * 1 ≤ (1 - 1 / 4) * borgAcct.capacity
      - borgAcct.idle / borgAcct.time :=
  borgAcct.goodput_le_of_waste huseful (by unfold borgAcct; norm_num)

/-- **The cliff needs the waste** (plateau converse, instantiated): a
scheduler offered 200 against capacity 100, at the uniform-loss equilibrium
`p = 1/2` with no rescheduling at all — if measured goodput falls below the
plateau value 100, the waste fraction is strictly positive. No waste, no
cliff: retries and preemption cannot dent throughput except by destroying
work.

Disclosed: every numeral here is fixed, so the hypothesis evaluates to
`(1-w)·100 < 100` — that is, to the conclusion. What the instantiation
records is that the plateau really does sit at 100 for *these* Borg numbers
(the `UniformLossEq` obligation below is where the work is); the implication
itself is immediate once it does. -/
theorem borg_cliff_needs_waste {w : ℝ} (hw : 0 ≤ w)
    (hcliff : (1 - w) * goodput {0} (fun _ => 200) (fun _ => 1) (1 / 2)
      < min (∑ _j ∈ ({0} : Finset ℕ), (200 : ℝ)) 100) : 0 < w := by
  refine cliff_implies_waste (fun j _ => le_rfl) (fun j _ => by norm_num) hw
    ?_ hcliff
  right
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold attemptRate
  rw [Finset.sum_singleton]
  norm_num [expAttempts_def]

/-!
## Preemption cascades as stack composition
-/

/-- **One inequality certifies the cascade.** A batch task evicted at the
band level retries placement up to 4 times; each placement failing at the
cell level retries up to 3 times. Whatever the per-attempt failure
probabilities and whatever the load-coupled kernel, offered load 2 with
composite amplification at most `4·3 = 12` gives `2·12 = 24 < 100`: the
assembled two-layer cascade has no congested equilibrium. The certificate
never inspects the kernel. -/
theorem borg_cascade_certified (p₁ p₂ : ℝ) (h₁ : p₁ ∈ Set.Icc (0 : ℝ) 1)
    (h₂ : p₂ ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℝ)
    (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))) :
    ¬(stackToLoop [⟨p₁, 4, h₁, by norm_num⟩, ⟨p₂, 3, h₂, by norm_num⟩]
        2 g (by norm_num) hg_mem hg_mono).CongestedEq 100 := by
  apply stack_budget_no_congestedEq
  have hle := layersAmp_le_prod_cap
    [⟨p₁, 4, h₁, by norm_num⟩, ⟨p₂, 3, h₂, by norm_num⟩]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    layersAmp_cons, layersAmp_nil, mul_one] at hle ⊢
  norm_num at hle
  linarith

/-!
## Quota as admission denomination
-/

/-- **Quota alone bounds nothing.** A tenant admitted 10 tasks/s of quota,
with unclamped rescheduling, can exceed any target placement load — here,
1000 placements/s from 10 tasks/s. Admission denominated in submissions is
blind to the amplification behind it. -/
theorem borg_quota_needs_clamp : ∃ A, 0 < A ∧ (1000 : ℝ) < 10 * A :=
  admission_needs_clamp (by norm_num) 1000

/-- **Quota plus a replacement clamp is a real bound**: 10 tasks/s of quota
under a 3-placement clamp is at most 30 placements/s, full stop. The pair
(quota, clamp) is the attempt-denominated admission control the scheduler
actually needs. -/
theorem borg_quota_bound {A : ℝ} (hA : A ≤ 3) : (10 : ℝ) * A ≤ 30 := by
  have h := admission_bound (Q := 10) (by norm_num) hA
  norm_num at h
  exact h

end Overload
