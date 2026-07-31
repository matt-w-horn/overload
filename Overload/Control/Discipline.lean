module

public import Overload.Basic -- shake: keep
public import Overload.Control.Priority
public import Overload.Loop.ClosedLoop
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

/-!
# Allocation disciplines: one interface, many priority languages

Different systems speak different allocation languages — priority bands,
fair shares, plain FIFO queues — and a theory pinned to any one of them
does not transfer. This module states the interface they all implement: a
`Discipline` is *any* feasible, work-conserving split of capacity across
classes. Theorems stated on the interface transfer across every allocation
language; theorems about a specific language attach to its instance.

Two instances close the loop with `Overload/Control/Priority.lean`, whose
two regimes turn out to be two disciplines:

* `strictDiscipline` — the intent-label strict-priority allocation
  (`Priority.alloc`/`residual`, wrapped over `Fin k`): isolation lives
  here (`top_class_isolation`).
* `propDiscipline` — attempts-proportional: each class receives its demand
  scaled by the common acceptance `min 1 (C/total)`. This is what a FIFO
  queue implements under storm; at offered attempts it *is* the
  uniform-loss `sharedGoodput` regime — the identity is
  `propDiscipline_alloc_eq_sharedGoodput` — where amplification is de
  facto priority (`effective_priority`) and floors come only from budgets
  (`budget_floor`, stated on the offered-attempts share).

The discipline-agnostic content: work conservation (`sum_alloc`,
`sum_alloc_le`) and the **per-class certificate**
(`Discipline.class_clamp_no_congestedEq`): whatever the allocation
language, a class running as a closed loop over its grant, clamped below
that grant, has no congested equilibrium there —
`borg_batch_over_residual` is its strict-priority instance.

Also here, because service *order* is a discipline too: the stale-first
waste channel. `fifo_head_expired` — backlog beyond `D·C` puts the FIFO
sojourn past the deadline, so a unit admitted there expires before
service, and under sustained backlog the unit now served is already
expired (the per-unit reading lives in `fifoSojourn`'s definition);
`lifoSojourn`/`lifo_fresh` record the newest-first contrast (the model
content is the definition; the inequality is bookkeeping). Adaptive LIFO
and controlled-delay queueing are the practice counterparts.

Max-min fairness (water-filling) is the named next instance, deliberately
not attempted in this pass.
-/

@[expose] public section

namespace Overload

/-- An allocation discipline over `k` classes: any feasible,
work-conserving split of capacity. Systems differ in which discipline
their "priority language" implements; theorems on this interface transfer
across all of them. -/
structure Discipline (k : ℕ) where
  /-- The allocation map: demands and capacity to per-class grants. -/
  alloc : (Fin k → ℝ) → ℝ → Fin k → ℝ
  /-- Grants are nonnegative on nonnegative data. -/
  alloc_nonneg : ∀ d C i, (∀ j, 0 ≤ d j) → 0 ≤ C → 0 ≤ alloc d C i
  /-- Feasibility: no class receives beyond its demand. -/
  alloc_le_demand : ∀ d C i, (∀ j, 0 ≤ d j) → 0 ≤ C → alloc d C i ≤ d i
  /-- Work conservation: grants exhaust `min(total demand, C)` — nothing
  stranded, nothing manufactured. -/
  sum_alloc : ∀ d C, (∀ j, 0 ≤ d j) → 0 ≤ C →
    ∑ i, alloc d C i = min (∑ i, d i) C

namespace Discipline

variable {k : ℕ} (D : Discipline k)

/-- Total grants never exceed capacity. -/
theorem sum_alloc_le (d : Fin k → ℝ) (C : ℝ) (hd : ∀ j, 0 ≤ d j)
    (hC : 0 ≤ C) : ∑ i, D.alloc d C i ≤ C := by
  rw [D.sum_alloc d C hd hC]
  exact min_le_right _ _

/-- **The discipline-agnostic per-class certificate**: whatever the
allocation language, a class running as a bounded loop over its grant,
clamped with `λ·K` below that grant, has no congested equilibrium there.
`borg_batch_over_residual` (`Overload/Examples/Borg.lean`) is the
strict-priority instance.

Two scopings, stated rather than implied. The class loop needs only
`BoundedLoop`, so a batching or backpressure class inherits the certificate.
And the *only* thing consumed from `D` is the numeric value of the grant
`D.alloc d C i` — none of `alloc_nonneg`, `alloc_le_demand`, `sum_alloc`
enters the proof. That is precisely why the certificate is
discipline-agnostic, and equally why it certifies nothing about the
allocation itself: feasibility and work conservation are the discipline's
own theorems, not this one's. -/
theorem class_clamp_no_congestedEq (L : BoundedLoop) {Kc : ℝ}
    (hclamp : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p ≤ Kc)
    (d : Fin k → ℝ) (C : ℝ) (i : Fin k)
    (hK : L.lam * Kc < D.alloc d C i) :
    ¬L.CongestedEq (D.alloc d C i) :=
  L.clamp_no_congestedEq hclamp hK

end Discipline

/-!
## Instance 1: strict priority
-/

/-- Zero-extension of `Fin k` demands to `ℕ`, for wrapping the ℕ-indexed
strict-priority allocation of `Overload/Control/Priority.lean`. -/
noncomputable def extendDemand {k : ℕ} (d : Fin k → ℝ) : ℕ → ℝ :=
  fun n => if h : n < k then d ⟨n, h⟩ else 0

/-- The zero-extension of nonnegative demands is nonnegative. -/
theorem extendDemand_nonneg {k : ℕ} {d : Fin k → ℝ} (hd : ∀ j, 0 ≤ d j)
    (n : ℕ) : 0 ≤ extendDemand d n := by
  unfold extendDemand
  split
  · exact hd _
  · exact le_rfl

/-- The `Finset.range k` sum of the zero-extension equals the `Fin k` sum of
the original demands. -/
theorem sum_extendDemand {k : ℕ} (d : Fin k → ℝ) :
    ∑ j ∈ Finset.range k, extendDemand d j = ∑ i, d i := by
  rw [← Fin.sum_univ_eq_sum_range (fun n => extendDemand d n) k]
  exact Finset.sum_congr rfl fun i _ => by simp [extendDemand]

/-- **Strict priority as a discipline**: the library's intent-label
allocation (`Priority.alloc`/`residual`), wrapped over `Fin k`. Isolation
(`top_class_isolation`) and no-stranding (`no_stranding`) are its
language-specific theorems. -/
noncomputable def strictDiscipline (k : ℕ) : Discipline k where
  alloc := fun d C i => alloc (extendDemand d) C i.val
  alloc_nonneg := fun d _C i hd _hC =>
    alloc_nonneg (extendDemand_nonneg hd) i.val
  alloc_le_demand := fun d C i _hd _hC => by
    have h := alloc_le_demand (demand := extendDemand d) (C := C) (j := i.val)
    rwa [show extendDemand d i.val = d i from by simp [extendDemand]] at h
  sum_alloc := fun d C hd hC => by
    have hstr := no_stranding (demand := extendDemand d) (C := C) hC
      (extendDemand_nonneg hd) k
    rw [sum_extendDemand] at hstr
    rw [← Fin.sum_univ_eq_sum_range
      (fun n => alloc (extendDemand d) C n) k] at hstr
    exact hstr

/-!
## Instance 2: attempts-proportional (what a FIFO queue implements)
-/

/-- **Attempts-proportional as a discipline**: each class receives its
demand scaled by the common acceptance `min 1 (C/total)` — the uniform-loss
`sharedGoodput` regime of `Overload/Control/Priority.lean`, reframed as an
allocation (`propDiscipline_alloc_eq_sharedGoodput` is the identity, at
demands read as offered attempts). Under it, share follows offered volume
(`effective_priority`, at nonzero acceptance) and floors come only from
budgets (`budget_floor`, stated on the offered-attempts share); there is no
isolation to be had from the resource itself. -/
noncomputable def propDiscipline (k : ℕ) : Discipline k where
  alloc := fun d C i => d i * min 1 (C / ∑ j, d j)
  alloc_nonneg := fun d C i hd hC =>
    mul_nonneg (hd i)
      (le_min zero_le_one
        (div_nonneg hC (Finset.sum_nonneg fun j _ => hd j)))
  alloc_le_demand := fun d _C i hd _hC =>
    mul_le_of_le_one_right (hd i) (min_le_left _ _)
  sum_alloc := fun d C hd hC => by
    have hS0 : 0 ≤ ∑ j, d j := Finset.sum_nonneg fun j _ => hd j
    rw [← Finset.sum_mul]
    rcases hS0.eq_or_lt with hS | hS
    · rw [← hS, zero_mul]
      exact (min_eq_left hC).symm
    · have hSne : (∑ j, d j) ≠ 0 := ne_of_gt hS
      rw [mul_min_of_nonneg 1 (C / ∑ j, d j) hS0, mul_one,
        mul_comm (∑ j, d j) (C / ∑ j, d j), div_mul_cancel₀ C hSne]

/-- **The bridge to the uniform-loss regime**: at demands read as offered
attempts, the proportional grant *is* `sharedGoodput` at acceptance
`min 1 (C/total)`. This is what lets `effective_priority` (at nonzero
acceptance) and `budget_floor` (an offered-attempts share) speak about the
instance. -/
theorem propDiscipline_alloc_eq_sharedGoodput {k : ℕ} (lam A : Fin k → ℝ)
    (C : ℝ) (i : Fin k) :
    (propDiscipline k).alloc (offeredAttempts lam A) C i
      = sharedGoodput lam A (min 1 (C / ∑ j, offeredAttempts lam A j)) i := by
  change offeredAttempts lam A i * min 1 (C / ∑ j, offeredAttempts lam A j)
    = min 1 (C / ∑ j, offeredAttempts lam A j) * offeredAttempts lam A i
  exact mul_comm _ _

/-!
## Service order: the stale-first waste channel
-/

/-- FIFO sojourn under backlog `Q`: the wait `Q / C` at drain rate `C` —
the queue a unit admitted at backlog `Q` must wait through; under
sustained backlog, equally the wait the unit now served has behind it. -/
noncomputable def fifoSojourn (Q C : ℝ) : ℝ := Q / C

/-- LIFO sojourn of the newest item: zero queueing wait — newest-first
serves fresh work whatever the backlog (at the stale work's expense). The
modeling content is this definition; `lifo_fresh` is its bookkeeping. -/
def lifoSojourn : ℝ := 0

/-- **FIFO stale service**: whenever backlog exceeds `D·C`, the FIFO
sojourn `Q/C` exceeds the deadline `D` — a unit admitted at such a
backlog expires before it is served, and under sustained backlog the
unit now served is already expired. The modeling content (the per-unit
reading, the stale-first waste
channel) is `fifoSojourn`'s definition; this inequality is its bookkeeping.
(Practice counterparts: adaptive LIFO, controlled-delay queueing.) -/
theorem fifo_head_expired {Q C D : ℝ} (hC : 0 < C) (h : D * C < Q) :
    D < fifoSojourn Q C := by
  rw [fifoSojourn, lt_div_iff₀ hC]
  linarith

/-- The LIFO contrast: the newest item's wait is within any nonnegative
deadline. -/
theorem lifo_fresh {D : ℝ} (hD : 0 ≤ D) : lifoSojourn ≤ D := hD

/-!
## Regressions
-/

/-- Numeric regression: proportional allocation at overload — demands
`(3, 9)` against capacity `4` grant the top class `1`, a third of its
ask. -/
theorem propDiscipline_alloc_at_overload :
    (propDiscipline 2).alloc ![3, 9] 4 0 = 1 := by
  norm_num [propDiscipline, Fin.sum_univ_two, min_def]

/-- Numeric regression: the same allocation is work-conserving — the grants
sum to the capacity `4`. -/
theorem propDiscipline_sum_alloc_at_overload :
    ∑ i, (propDiscipline 2).alloc ![3, 9] 4 i = 4 := by
  rw [(propDiscipline 2).sum_alloc ![3, 9] 4
    (Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩) (by norm_num)]
  norm_num [Fin.sum_univ_two, min_def]

/-- Numeric regression on the interface bound at underload: demands `(1, 2)`
against capacity `10` grant `3` in total, so `sum_alloc_le`'s ceiling is slack
by `7` — the bound is a ceiling, not the allocation. -/
theorem propDiscipline_sum_alloc_le_at_underload :
    ∑ i, (propDiscipline 2).alloc ![1, 2] 10 i ≤ 10 ∧
      ∑ i, (propDiscipline 2).alloc ![1, 2] 10 i = 3 := by
  refine ⟨(propDiscipline 2).sum_alloc_le ![1, 2] 10
    (Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩) (by norm_num), ?_⟩
  rw [(propDiscipline 2).sum_alloc ![1, 2] 10
    (Fin.forall_fin_two.mpr ⟨by norm_num, by norm_num⟩) (by norm_num)]
  norm_num [Fin.sum_univ_two, min_def]

/-- Numeric regression on the discipline-agnostic per-class certificate: the
top class's grant of `1` at those demands carries a class loop clamped at
`λ·K = 1/2`, so that class has no congested equilibrium against its own
grant — and the discipline's own theorems are not what makes it hold. -/
theorem class_clamp_at_overload :
    ¬(stepLoop (1 / 4) 10 2 (by norm_num) (by norm_num)).CongestedEq
      ((propDiscipline 2).alloc ![3, 9] 4 0) :=
  (propDiscipline 2).class_clamp_no_congestedEq (Kc := 2)
    (stepLoop (1 / 4) 10 2 (by norm_num) (by norm_num)).toBoundedLoop
    (fun p hp => by
      change (1 : ℝ) + p * (2 - 1) ≤ 2
      linarith [hp.2])
    ![3, 9] 4 0
    (by
      change (1 : ℝ) / 4 * 2 < (propDiscipline 2).alloc ![3, 9] 4 0
      rw [propDiscipline_alloc_at_overload]
      norm_num)

/-- Numeric regression on the service-order pair: at backlog `25` and drain
rate `10`, the unit FIFO serves next has waited past its `2`-second deadline,
while the unit LIFO serves next is inside it. Same queue, same instant. -/
theorem service_order_at_backlog :
    (2 : ℝ) < fifoSojourn 25 10 ∧ lifoSojourn ≤ 2 :=
  ⟨fifo_head_expired (by norm_num) (by norm_num), lifo_fresh (by norm_num)⟩

/-- Numeric regression: strict priority at the same numbers grants the top
class its full `3` — the languages differ, the interface holds for both. -/
theorem strictDiscipline_alloc_at_overload :
    (strictDiscipline 2).alloc ![3, 9] 4 0 = 3 := by
  change alloc (extendDemand ![3, 9]) 4 0 = 3
  rw [top_class_isolation (by norm_num)]
  norm_num [extendDemand, min_def]

end Overload
