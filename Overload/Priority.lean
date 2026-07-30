import Mathlib
import Overload.Amplification
import Overload.Deadline

/-!
# Multi-class contention: amplification as effective priority

Several request classes share one bottleneck of capacity `C`. Class `j` offers
`lam j` requests per unit time and amplifies each by `A j` (its expected
attempts per request). This module is the multi-class consequence of the
capacity-conservation invariant: channel-3 demand lands on *shared* capacity, so when the resource
cannot discriminate under storm, class outcomes order by offered **attempts**
`lam j · A j`, not by intended priority.

Two contention regimes, each with theorems:

**Undiscriminating contention** (the resource cannot tell classes apart):
* `effective_priority` — under a common acceptance probability, a class's
  goodput share is its *attempt* share. Amplification is de facto priority.
* `inversion` — **the priority-inversion construction**: for any two classes
  and any target, a large enough low-class amplification drives the high
  class's goodput share below that target. Realizable up to the configured
  cap, and no further: `Deadline.neff_ge_of_fast` supplies any target attempt
  count *below the cap* once rejection is cheap enough, while
  `Deadline.neff_le` bounds attempts by the cap whatever the latency. The
  amplification `inversion_threshold` asks for therefore has to come from a
  cap that large, or from caps multiplied across layers — not from fast
  rejection on its own.
* `budget_floor` — **isolation from budgets alone**: per-class clamps
  `A j ≤ 1 + β j` give every class an explicit goodput-share floor, with *no*
  priority enforcement at the resource.

**Priority at the boundary from intent labels** (the fix): a strict-priority
residual allocation.
* `alloc_le_demand`, `alloc_le_residual` — the allocation is feasible.
* `no_stranding` — total allocation is `min (∑ demand) C`: work-conserving,
  so idle capacity is never stranded. The utilization objection, answered as
  a theorem.
* `top_class_isolation` — the highest-priority class receives
  `min (demand 0) C` **regardless of every lower class's amplification**. The
  formal content of "enforce priority from intent and the top tier is immune
  to a lower tier's retry storm".

Plus:
* `eligibility_gate` — a class whose retries are disabled (`cap = 1`) has
  `A = 1`: "this class never retries" as a machine-checked fact.
* `admission_bound` / `admission_needs_clamp` — **admission denomination**: a
  cap on admitted *requests* bounds attempt load iff amplification is clamped;
  request-denominated admission control is blind to amplification behind it.

Neutral queueing vocabulary throughout; the multi-tenant reading lives only in
`Examples/Borg.lean`.

**Composing with the equilibrium machinery**: the allocation side hands each
class a capacity (`alloc`/`residual`), and each class then runs as its own
closed loop *over that capacity* — instantiate any `ClosedLoop` theorem with
threshold `Θ := residual demand C j`. `borg_batch_over_residual` in
`Examples/Borg.lean` is the worked instance (a clamp certificate over the
batch band's residual capacity).

**Priority is one allocation language among several.** The interface both
of this module's regimes implement — any feasible, work-conserving split —
lives in `Overload/Discipline.lean`: strict priority (`strictDiscipline`)
and the undiscriminating/attempts-proportional regime (`propDiscipline`,
what a FIFO queue does under storm) are its two instances, and the
per-class clamp certificate is stated once on the interface.
-/

namespace Overload

variable {k : ℕ}

/-- Offered attempt rate of class `j`: requests times amplification. -/
def offeredAttempts (lam A : Fin k → ℝ) (j : Fin k) : ℝ := lam j * A j

/-!
## Undiscriminating contention
-/

/-- Goodput of class `j` under a common acceptance probability `ρ` (the
resource, blind to class, accepts every attempt with the same probability):
accepted attempts that were the request's success. We take goodput
proportional to the offered attempt rate — the undiscriminating limit. -/
def sharedGoodput (lam A : Fin k → ℝ) (ρ : ℝ) (j : Fin k) : ℝ :=
  ρ * offeredAttempts lam A j

/-- **Amplification is effective priority.** Under undiscriminating
contention, the goodput ratio between two classes is their *attempt* ratio —
intended priority never enters. A low-priority class that amplifies hard
outranks a high-priority class that does not. (The identity is unconditional:
when class `i` offers nothing, both sides are `0` by the division-by-zero
convention, and the ratio reading is vacuous — apply it only to classes with
positive offered attempts.) -/
theorem effective_priority (lam A : Fin k → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0)
    {i j : Fin k} :
    sharedGoodput lam A ρ j / sharedGoodput lam A ρ i
      = offeredAttempts lam A j / offeredAttempts lam A i := by
  unfold sharedGoodput
  rw [mul_div_mul_left _ _ hρ]

/-- **The inversion threshold, named.** The existential in `inversion` hides
where the starvation begins; here it is explicit and one-sided: *every*
low-class amplification past `λ_hi·A_hi / (λ_lo·ε)` drives the high class's
share of total offered attempts below `ε`. Sizing a low tier's retry budget against
this threshold is the checkable form of the construction. -/
theorem inversion_threshold {lam Ahi lamlo ε Alo : ℝ} (hlamhi : 0 < lam)
    (hAhi : 0 < Ahi) (hlamlo : 0 < lamlo) (hε : 0 < ε)
    (hAlo : lam * Ahi / (lamlo * ε) < Alo) :
    (lam * Ahi) / (lam * Ahi + lamlo * Alo) < ε := by
  have hN : 0 < lam * Ahi := mul_pos hlamhi hAhi
  have hle : 0 ≤ lam * Ahi / (lamlo * ε) := by positivity
  have hAlo0 : 0 < Alo := lt_of_le_of_lt hle hAlo
  have hden : 0 < lam * Ahi + lamlo * Alo := by positivity
  have hkey : lam * Ahi < Alo * (lamlo * ε) := by
    have h := mul_lt_mul_of_pos_right hAlo (by positivity : (0 : ℝ) < lamlo * ε)
    rwa [div_mul_cancel₀ _ (by positivity : lamlo * ε ≠ 0)] at h
  rw [div_lt_iff₀ hden]
  nlinarith [mul_pos hε hN]

/-- **The priority-inversion construction.** Fix a high class `hi` with
positive offered load and any target share `ε > 0`. A large enough low-class
amplification drives the high class's fraction of total offered attempts
below `ε` — its goodput fraction too, since `sharedGoodput` scales every
class by the same `ρ`.
Amplification alone — with no change to intended priority — starves the high
class. One step past the named threshold suffices. -/
theorem inversion {lam Ahi : ℝ} (hlamhi : 0 < lam) (hAhi : 0 < Ahi)
    {lamlo : ℝ} (hlamlo : 0 < lamlo) {ε : ℝ} (hε : 0 < ε) :
    ∃ Alo, 0 < Alo ∧
      (lam * Ahi) / (lam * Ahi + lamlo * Alo) < ε :=
  ⟨lam * Ahi / (lamlo * ε) + 1, by positivity,
    inversion_threshold hlamhi hAhi hlamlo hε (lt_add_one _)⟩

/-- Pin of the threshold at unit rates and `ε = 1/10`: the threshold sits at
`10`, so a low class amplifying by `11` takes the high class's share of
offered attempts to `1/12` — inside the `1/10` starvation bound. -/
theorem inversion_threshold_pin :
    ((1 : ℝ) * 1) / (1 * 1 + 1 * 11) < 1 / 10 :=
  inversion_threshold one_pos one_pos one_pos (by norm_num) (by norm_num)

/-- **Isolation from per-class budgets alone.** If every class is clamped to
`A j ≤ 1 + β j`, then class `i`'s share of total offered attempts is at least
`lam i / ∑ lam j (1 + β j)` — a positive floor with no priority enforcement
at the resource. Budgets bound the arms race even when the resource stays
blind. -/
theorem budget_floor {lam A β : Fin k → ℝ} (hlam : ∀ j, 0 ≤ lam j)
    (hA1 : ∀ j, 1 ≤ A j) (hclamp : ∀ j, A j ≤ 1 + β j) (i : Fin k)
    (hlami : 0 < lam i) :
    lam i / (∑ j, lam j * (1 + β j))
      ≤ offeredAttempts lam A i / (∑ j, offeredAttempts lam A j) := by
  have hnn : ∀ j, 0 ≤ offeredAttempts lam A j := fun j =>
    mul_nonneg (hlam j) (le_trans zero_le_one (hA1 j))
  have hden2 : 0 < ∑ j, offeredAttempts lam A j := by
    refine Finset.sum_pos' (fun j _ => hnn j) ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos hlami (lt_of_lt_of_le zero_lt_one (hA1 i))
  have hoffi : lam i ≤ offeredAttempts lam A i :=
    le_mul_of_one_le_right (hlam i) (hA1 i)
  have hsum_le : ∑ j, offeredAttempts lam A j ≤ ∑ j, lam j * (1 + β j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    unfold offeredAttempts
    exact mul_le_mul_of_nonneg_left (hclamp j) (hlam j)
  exact div_le_div₀ (hnn i) hoffi hden2 hsum_le

/-!
## Priority at the boundary from intent labels

Strict-priority residual allocation: class `0` (highest priority) is served
first from capacity `C`, class `1` from what remains, and so on. Classes are
indexed by `ℕ` (zero-extended demand); the served set is `0, …, k-1`.
Amplification is irrelevant here — allocation is driven by the *intent*
demand, not the wire attempt rate.
-/

/-- Capacity left after fully accounting for the demand of the strictly
higher-priority classes `0, …, m-1`, clamped at zero. -/
def residual (demand : ℕ → ℝ) (C : ℝ) (m : ℕ) : ℝ :=
  max 0 (C - ∑ j ∈ Finset.range m, demand j)

/-- Allocation to class `j`: its demand or the residual above it, whichever
is smaller. -/
def alloc (demand : ℕ → ℝ) (C : ℝ) (j : ℕ) : ℝ :=
  min (demand j) (residual demand C j)

/-- The residual is nonnegative, by its clamp at zero. -/
theorem residual_nonneg (demand : ℕ → ℝ) (C : ℝ) (m : ℕ) :
    0 ≤ residual demand C m := le_max_left _ _

/-- The allocation is nonnegative on nonnegative demand. -/
theorem alloc_nonneg {demand : ℕ → ℝ} {C : ℝ} (hd : ∀ j, 0 ≤ demand j)
    (j : ℕ) : 0 ≤ alloc demand C j :=
  le_min (hd j) (residual_nonneg demand C j)

/-- Feasibility, demand side: no class receives beyond its demand. -/
theorem alloc_le_demand {demand : ℕ → ℝ} {C : ℝ} (j : ℕ) :
    alloc demand C j ≤ demand j := min_le_left _ _

/-- Feasibility, residual side: no class receives beyond the residual above
it. -/
theorem alloc_le_residual {demand : ℕ → ℝ} {C : ℝ} (j : ℕ) :
    alloc demand C j ≤ residual demand C j := min_le_right _ _

/-- Pin of the residual bound at overload: the top class takes `3` of capacity
`4`, so class `1` is held to the leftover `1` however large its own demand —
here `9`, nine times what the residual can serve. -/
theorem alloc_le_residual_pin :
    alloc (fun j => if j = 0 then (3 : ℝ) else 9) 4 1 ≤ 1 :=
  (alloc_le_residual 1).trans (by unfold residual; norm_num)

/-- **The highest-priority class is isolated from all lower classes.** Class
`0` receives `min (demand 0) C` — determined entirely by its own demand and
capacity, with *no dependence on any lower class's demand or amplification*.
Enforcing priority from intent labels makes the top class immune to a lower
class's retry storm. -/
theorem top_class_isolation {demand : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) :
    alloc demand C 0 = min (demand 0) C := by
  unfold alloc residual
  simp [max_eq_right hC]

/-- **Work conservation: no stranding.** The total allocation across the first
`k` classes equals `min (∑_{j<k} demand) C`. Lower classes borrow idle
capacity freely; nothing is left idle while demand waits. This answers the
utilization objection to strict priority — as a theorem, not a promise. -/
theorem no_stranding {demand : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ j, 0 ≤ demand j) (k : ℕ) :
    ∑ j ∈ Finset.range k, alloc demand C j
      = min (∑ j ∈ Finset.range k, demand j) C := by
  induction k with
  | zero => simp [min_eq_left hC]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    -- Let S = ∑_{j<n} demand, d = demand n. Goal:
    --   min S C + alloc n = min (S + d) C, with alloc n = min d (max 0 (C-S)).
    set S := ∑ j ∈ Finset.range n, demand j with hS
    have hdn : 0 ≤ demand n := hd n
    unfold alloc residual
    rw [← hS]
    rcases le_or_gt S C with hSC | hSC
    · rw [min_eq_left hSC, max_eq_right (by linarith)]
      rcases le_or_gt (demand n) (C - S) with hd1 | hd1
      · rw [min_eq_left hd1, min_eq_left (by linarith)]
      · rw [min_eq_right (le_of_lt hd1), min_eq_right (by linarith)]
        ring
    · rw [min_eq_right (le_of_lt hSC), max_eq_left (by linarith),
        min_eq_right hdn, min_eq_right (by linarith)]
      ring

/-!
## Eligibility gating and admission denomination
-/

/-- **Eligibility gate.** A class whose retries are disabled (attempt cap 1)
amplifies by exactly 1, whatever its failure probability: "this class never
retries" as a machine-checked fact, not tribal knowledge. Arithmetically this
is Mathlib's `geom_sum_one` at the definition of `expAttempts`; the name
carries the demand-side reading of the eligibility lever. -/
theorem eligibility_gate (p : ℝ) : expAttempts p 1 = 1 :=
  (expAttempts_def p 1).trans (geom_sum_one p)

/-- Pin of the gate outside the probability range. `expAttempts` is total, so
the cap-1 identity survives the junk argument `p = 7`: the cap alone carries
it, and no hypothesis on `p` is doing hidden work. -/
theorem eligibility_gate_pin : expAttempts 7 1 = 1 := eligibility_gate 7

/-- **Admission denomination, the bound.** A per-request admission cap `Q`
combined with an amplification clamp `A ≤ K` bounds the attempt load at
`Q · K`. Admission control denominated in requests only works when paired
with a bound on amplification. -/
theorem admission_bound {Q A K : ℝ} (hQ : 0 ≤ Q) (hAK : A ≤ K) :
    Q * A ≤ Q * K := mul_le_mul_of_nonneg_left hAK hQ

/-- **Admission denomination, the gap.** Without an amplification clamp,
attempt load `Q · A` is unbounded as `A` grows even at fixed admitted-request
rate `Q > 0`: request-denominated admission is blind to the amplification
behind it. For any target load there is an amplification that exceeds it. -/
theorem admission_needs_clamp {Q : ℝ} (hQ : 0 < Q) (M : ℝ) :
    ∃ A, 0 < A ∧ M < Q * A := by
  refine ⟨(max M 0) / Q + 1, by positivity, ?_⟩
  have h1 : Q * ((max M 0) / Q + 1) = max M 0 + Q := by
    field_simp
  rw [h1]
  have : M ≤ max M 0 := le_max_left _ _
  linarith

end Overload
