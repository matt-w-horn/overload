import Mathlib
import Overload.Amplification

/-!
# Composition of amplification across layers

A request enters a stack of retry mechanisms; each attempt at a layer spawns
attempts at the layer below. This file establishes the multiplicative
composition law and its honest failure conditions, working with
finite expectations as weighted `Finset` sums — the deadline bounds every
attempt count, so no measure theory is needed.

* `wald_bounded` — the **constant-cost core of Wald's identity**:
  `E[K·μ] = E[K]·μ` for a finitely-supported count `K` and a fixed per-item
  cost `μ`. This is deliberately the deterministic-cost case — the
  probabilistic content of the full identity is whether a *single* `μ` is the
  right per-attempt cost across the count distribution.
* `branching_wald` / `branching_wald_single` — the **two-level identity,
  derived**: `E[∑_{j<K} Xⱼ] = E[K]·E[X]` from an explicit joint model, with
  the per-slot product form of the joint as the load-bearing independence
  hypothesis, and `coupled_weight_breaks_wald` the numeric joint whose own
  marginals violate the conclusion.
* `stackAmp` — layered composition as the **modeling definition**:
  `∏ E[Kᵢ]` bottom attempts per request, with the bounds `one_le_stackAmp`
  and `stackAmp_le_prod_cap` (the forced-failure envelope). The
  derivation of the product from per-layer Wald conditions is *assumed by
  this definition*, not derived here.
* `doomedAmp` / `doomed_worsens` — the within-request correlation correction:
  a "doomed" fraction `d` (requests that fail every attempt) gives
  `E[A] = (1-d)·A_indep + d·∏nᵢ`, and correlation *only increases*
  amplification. The i.i.d. assumption is the most flattering one available
  to retries.
* `shared_budget_breaks_wald` — a concrete two-request model where a shared
  budget couples the counts, so the joint attempt total falls strictly below
  the sum of the independent per-request totals: per-request marginal
  accounting (the product/sum-of-marginals bookkeeping behind `stackAmp`)
  overcounts under shared stopping state.
-/

namespace Overload

/-- Expectation of a finitely-supported count distribution given as a weight
function `P : ℕ → ℝ` on `Finset.range (N+1)` (probabilities of `0, …, N`
attempts). -/
def expOf (N : ℕ) (P : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (N + 1), (k : ℝ) * P k

/-- **The constant-cost core of Wald's identity.** If a request makes `K`
attempts (count distribution `P` on `0…N`) and every attempt costs exactly
`μ`, the expected total cost is `E[K]·μ`. This is an unconditional linearity
identity — no independence hypothesis appears, because the deterministic
per-item cost bakes it in; whether one fixed `μ` is the right per-attempt
cost for a real workload is a modeling judgment made where `μ` is measured. -/
theorem wald_bounded (N : ℕ) (P : ℕ → ℝ) (μ : ℝ) :
    ∑ k ∈ Finset.range (N + 1), P k * ((k : ℝ) * μ) = expOf N P * μ := by
  unfold expOf
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Pin of the constant-cost identity at a uniform count on `{0, 1, 2}` and a
per-attempt cost of `5`: the expected total is `5`, which is `E[K]·μ` at
`E[K] = 1`. -/
theorem wald_bounded_pin :
    ∑ k ∈ Finset.range (2 + 1), (1 / 3 : ℝ) * ((k : ℝ) * 5) = 5 := by
  rw [wald_bounded 2 (fun _ => (1 / 3 : ℝ)) 5]
  norm_num [expOf, Finset.sum_range_succ]

/-- Layered amplification composes multiplicatively: the expected number of
bottom-layer attempts per request is the product of the per-layer expected
attempt counts (under the i.i.d.-layers Wald conditions). Here
layer `i` has i.i.d. per-attempt failure probability `p i` and cap `n i`. -/
def stackAmp {ι : Type*} (s : Finset ι) (p : ι → ℝ) (n : ι → ℕ) : ℝ :=
  ∏ i ∈ s, expAttempts (p i) (n i)

/-- Layered amplification is at least 1: retries never reduce the attempt
count below one per request. -/
theorem one_le_stackAmp {ι : Type*} (s : Finset ι) {p : ι → ℝ} {n : ι → ℕ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hn : ∀ i ∈ s, 1 ≤ n i) : 1 ≤ stackAmp s p n := by
  have h : ∏ _i ∈ s, (1 : ℝ) ≤ stackAmp s p n :=
    Finset.prod_le_prod (fun _ _ => zero_le_one)
      (fun i hi => one_le_expAttempts (hp i hi) (hn i hi))
  simpa using h

/-- Layered amplification is bounded by the product of caps (the forced-failure
envelope: every attempt failing gives exactly `∏ nᵢ`). -/
theorem stackAmp_le_prod_cap {ι : Type*} (s : Finset ι) {p : ι → ℝ}
    (n : ι → ℕ) (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    stackAmp s p n ≤ ∏ i ∈ s, (n i : ℝ) :=
  Finset.prod_le_prod
    (fun i hi => expAttempts_nonneg (hp0 i hi) (n i))
    (fun i hi => expAttempts_le_cap (hp0 i hi) (hp1 i hi) (n i))

/-- Pin of both range bounds at two layers with cap `2` and per-attempt
failure probability `1/2`: the stack sits between the floor `1` and the
forced-failure envelope `∏ nᵢ = 4`. -/
theorem stackAmp_range_pin :
    1 ≤ stackAmp (Finset.univ : Finset (Fin 2)) (fun _ => 1 / 2) (fun _ => 2) ∧
      stackAmp (Finset.univ : Finset (Fin 2)) (fun _ => 1 / 2) (fun _ => 2)
        ≤ 4 := by
  refine ⟨one_le_stackAmp _ (fun _ _ => by norm_num) (fun _ _ => by norm_num),
    (stackAmp_le_prod_cap _ _ (fun _ _ => by norm_num)
      (fun _ _ => by norm_num)).trans ?_⟩
  norm_num [Fin.prod_univ_two]

/-!
## The doomed-request mixture

The i.i.d.-across-attempts assumption fails for "doomed" requests that fail
every attempt for a request-intrinsic reason, burning the cap at every layer.
The honest model mixes: fraction `d` doomed (attempt count `= ∏ nᵢ`), fraction
`1-d` behaving i.i.d. (attempt count `= A_indep`).
-/

/-- Expected amplification under the doomed mixture:
`(1-d)·A_indep + d·A_cap` for a doomed fraction `d`. -/
def doomedAmp (d Aindep Acap : ℝ) : ℝ := (1 - d) * Aindep + d * Acap

/-- **Correlation only worsens amplification.** Since a doomed request
exhausts every cap (`A_indep ≤ ∏ nᵢ = A_cap`), the doomed mixture's mean
amplification is at least the i.i.d. value. Measuring the attempt-count
distribution rather than assuming its i.i.d. shape can only reveal *more*
amplification, never less. (The algebra needs only `0 ≤ d`; the probability
reading `d ≤ 1` is interpretation, not hypothesis.) -/
theorem doomed_worsens {d Aindep Acap : ℝ} (hd0 : 0 ≤ d)
    (hle : Aindep ≤ Acap) : Aindep ≤ doomedAmp d Aindep Acap := by
  unfold doomedAmp
  linarith [mul_nonneg hd0 (sub_nonneg.mpr hle)]

/-- Pin of the correlation bound at a quarter doomed, and again at the
disclosed corner `d = 3` outside the probability range: the algebra assumes
only `0 ≤ d`, so the bound holds there too. -/
theorem doomed_worsens_pin :
    (2 : ℝ) ≤ doomedAmp (1 / 4) 2 6 ∧ (2 : ℝ) ≤ doomedAmp 3 2 6 :=
  ⟨doomed_worsens (by norm_num) (by norm_num),
    doomed_worsens (by norm_num) (by norm_num)⟩

/-!
## Shared state breaks the product formula

A budget token bucket shared across requests couples their attempt counts, so
the per-request expectation no longer factors. The model: two requests, each
making one base attempt (`1`) plus a retry (`+1`) gated by a retry indicator
`r i ∈ {0,1}`. Independently both retry, for total `4`. A shared single-token
budget forces `r 0 + r 1 ≤ 1`, capping the joint total at `3 < 4`.
-/

/-- Total attempts for two requests with base attempt 1 each and retry
indicators `r 0, r 1`. -/
def twoReqTotal (r : Fin 2 → ℕ) : ℕ := 2 + r 0 + r 1

/-- Independently, both requests are retry-eligible: total `4`. -/
theorem twoReqTotal_indep : twoReqTotal ![1, 1] = 4 := rfl

/-- **Shared stopping state breaks per-request accounting.** Under a shared
single-token budget (`r 0 + r 1 ≤ 1`), the joint attempt total is at most `3`
— strictly below the independent total of `4`. Summing each request's
independent attempt count (the bookkeeping behind `stackAmp`'s product form)
overcounts the coupled system: shared stopping state must be conditioned on.
`coupled_weight_breaks_wald` below is the same
coupling at the level of the Wald identity itself. -/
theorem shared_budget_breaks_wald {r : Fin 2 → ℕ} (hbudget : r 0 + r 1 ≤ 1) :
    twoReqTotal r < twoReqTotal ![1, 1] := by
  rw [twoReqTotal_indep]
  unfold twoReqTotal
  omega

/-- Pin of the coupling at the budget's own arithmetic: when the single token
goes to the first request, the coupled total sits strictly below the
two-token total. -/
theorem shared_budget_breaks_wald_pin :
    twoReqTotal ![1, 0] < twoReqTotal ![1, 1] :=
  shared_budget_breaks_wald (by norm_num)

/-!
## Branching Wald: the two-level identity, derived

`wald_bounded` is the constant-cost bookkeeping identity. This section
derives the genuine two-level form `E[∑_{j<K} Xⱼ] = E[K]·E[X]` from an
explicit finite joint model. The total cost is decomposed per attempt slot
(`∑ⱼ Xⱼ·1_{j<K}` — pure linearity, valid for every joint law), and the
probabilistic content enters as the **per-slot product form** of the joint
weight (`w j k i = P k · Q i`: the count never reads a slot's cost draw).
That hypothesis is real: `coupled_weight_breaks_wald` exhibits a joint whose
own marginals violate the conclusion. The k-layer product `stackAmp` remains
the modeling definition; this is its finite honest core.
-/

/-- Expectation of a cost `x` under a finitely-supported weight `Q` on `s`.
The mean reading needs `∑ Q = 1`, supplied by callers where they need it. -/
def expCostOf {ι : Type*} (s : Finset ι) (Q x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, Q i * x i

/-- Indicator-count helper: `∑_{j<N} 1_{j<k}·c = k·c` for `k ≤ N`. -/
theorem sum_range_indicator_lt {c : ℝ} {k N : ℕ} (hk : k ≤ N) :
    ∑ j ∈ Finset.range N, (if j < k then c else 0) = (k : ℝ) * c := by
  have hsub : Finset.range k ⊆ Finset.range N := fun j hj =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
  rw [← Finset.sum_subset hsub ?vanish]
  case vanish =>
    intro j _hjN hjk
    exact if_neg fun h => hjk (Finset.mem_range.mpr h)
  rw [Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.mp hj),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Branching Wald, derived.** With the joint weight in per-slot product
form (`w j k i = P k · Q i` — slot `j`'s cost draw is independent of the
count), the expected total cost `E[∑_{j<K} Xⱼ]` equals `E[K]·E[X]`. The
product form is the load-bearing independence hypothesis; see
`coupled_weight_breaks_wald` for its necessity. -/
theorem branching_wald {ι : Type*} (N : ℕ) (s : Finset ι) (P : ℕ → ℝ)
    (Q x : ι → ℝ) (w : ℕ → ℕ → ι → ℝ)
    (hw : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range (N + 1), ∀ i ∈ s,
      w j k i = P k * Q i) :
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (N + 1), ∑ i ∈ s,
        w j k i * (if j < k then x i else 0)
      = expOf N P * expCostOf s Q x := by
  have step1 : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range (N + 1),
      (∑ i ∈ s, w j k i * (if j < k then x i else 0))
        = (if j < k then P k * expCostOf s Q x else 0) := by
    intro j hj k hk
    by_cases hjk : j < k
    · rw [if_pos hjk, expCostOf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hw j hj k hk i hi, if_pos hjk]
      ring
    · rw [if_neg hjk]
      refine Finset.sum_eq_zero fun i _hi => ?_
      rw [if_neg hjk, mul_zero]
  calc ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (N + 1), ∑ i ∈ s,
        w j k i * (if j < k then x i else 0)
      = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range (N + 1),
          (if j < k then P k * expCostOf s Q x else 0) :=
        Finset.sum_congr rfl fun j hj =>
          Finset.sum_congr rfl fun k hk => step1 j hj k hk
    _ = ∑ k ∈ Finset.range (N + 1), ∑ j ∈ Finset.range N,
          (if j < k then P k * expCostOf s Q x else 0) := Finset.sum_comm
    _ = ∑ k ∈ Finset.range (N + 1), (k : ℝ) * (P k * expCostOf s Q x) :=
        Finset.sum_congr rfl fun k hk =>
          sum_range_indicator_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range (N + 1), (k : ℝ) * P k) * expCostOf s Q x := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = expOf N P * expCostOf s Q x := rfl

/-- Single-draw form: one cost draw per request, total `K·X`. Bilinearity
once the joint factors; the product-form hypothesis is the content. -/
theorem branching_wald_single {ι : Type*} (N : ℕ) (s : Finset ι) (P : ℕ → ℝ)
    (Q x : ι → ℝ) (w : ℕ → ι → ℝ)
    (hw : ∀ k ∈ Finset.range (N + 1), ∀ i ∈ s, w k i = P k * Q i) :
    ∑ k ∈ Finset.range (N + 1), ∑ i ∈ s, w k i * ((k : ℝ) * x i)
      = expOf N P * expCostOf s Q x := by
  calc ∑ k ∈ Finset.range (N + 1), ∑ i ∈ s, w k i * ((k : ℝ) * x i)
      = ∑ k ∈ Finset.range (N + 1), (k : ℝ) * P k * (∑ i ∈ s, Q i * x i) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hw k hk i hi]
        ring
    _ = (∑ k ∈ Finset.range (N + 1), (k : ℝ) * P k) * (∑ i ∈ s, Q i * x i) :=
        (Finset.sum_mul _ _ _).symm
    _ = expOf N P * expCostOf s Q x := rfl

/-- The coupled joint: mass 1/2 on (1 attempt, cost 2) and 1/2 on
(2 attempts, cost 1) — a shared budget affords the second attempt only when
attempts are cheap. -/
noncomputable def coupledW (k : ℕ) (i : Fin 2) : ℝ :=
  if k = 1 ∧ i = 0 then 1 / 2 else if k = 2 ∧ i = 1 then 1 / 2 else 0

/-- Costs for the coupled joint. -/
noncomputable def coupledX : Fin 2 → ℝ := ![2, 1]

/-- **The product form cannot be dropped.** The coupled joint's true
expected total is `2`, while the product of its *own marginals* is `9/4` —
so the failure is not a bookkeeping trick, and the Wald conclusion is
genuinely false without per-slot independence. Same coupling mechanism as
`shared_budget_breaks_wald`, now at the level of the identity itself. -/
theorem coupled_weight_breaks_wald :
    ∑ k ∈ Finset.range 3, ∑ i, coupledW k i * ((k : ℝ) * coupledX i)
      ≠ expOf 2 (fun k => ∑ i, coupledW k i)
          * expCostOf Finset.univ
              (fun i => ∑ k ∈ Finset.range 3, coupledW k i) coupledX := by
  norm_num [coupledW, coupledX, expOf, expCostOf, Fin.sum_univ_two,
    Finset.sum_range_succ]

/-- Numeric regression, non-vacuity: the product-form hypothesis is
satisfiable — uniform count on `{0,1,2}`, uniform cost draw — so the
two-level identity holds at those constants. -/
theorem branching_wald_uniform :
    ∑ k ∈ Finset.range (2 + 1), ∑ i,
        ((1 / 3 : ℝ) * (1 / 2)) * ((k : ℝ) * coupledX i)
      = expOf 2 (fun _ => (1 / 3 : ℝ))
          * expCostOf Finset.univ (fun _ => (1 / 2 : ℝ)) coupledX :=
  branching_wald_single 2 Finset.univ (fun _ => (1 / 3 : ℝ))
    (fun _ => (1 / 2 : ℝ)) coupledX (fun _ _ => (1 / 3 : ℝ) * (1 / 2))
    (fun _ _ _ _ => rfl)

/-- Pin of the two-slot form at the same uniform constants: count uniform on
`{0, 1, 2}`, cost draw uniform on the two costs, joint factoring as
`1/3 · 1/2`. The expected total is `3/2`. -/
theorem branching_wald_pin :
    ∑ j ∈ Finset.range 2, ∑ k ∈ Finset.range (2 + 1), ∑ i,
        (1 / 6 : ℝ) * (if j < k then coupledX i else 0) = 3 / 2 :=
  (branching_wald 2 Finset.univ (fun _ => (1 / 3 : ℝ)) (fun _ => (1 / 2 : ℝ))
    coupledX (fun _ _ _ => (1 / 6 : ℝ))
    (fun _ _ _ _ _ _ => by norm_num)).trans (by
      norm_num [expOf, expCostOf, coupledX, Fin.sum_univ_two,
        Finset.sum_range_succ])

/-- Numeric regression: at the uniform constants the identity's right-hand
side computes to `E[K]·E[X] = 3/2`. -/
theorem uniform_wald_product_eq : expOf 2 (fun _ => (1 / 3 : ℝ))
    * expCostOf Finset.univ (fun _ => (1 / 2 : ℝ)) coupledX = 3 / 2 := by
  norm_num [expOf, expCostOf, coupledX, Fin.sum_univ_two,
    Finset.sum_range_succ]

end Overload
