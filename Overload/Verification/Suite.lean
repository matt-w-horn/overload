module

public import Overload.Basic -- shake: keep
public import Overload.Retry.Composition
public import Overload.Capacity.Conservation
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
# The verification suite: falsifiable invariants for simulators and systems

A simulator (or an instrumented production system) of this class is
wrong if it violates any of a short list of conservation laws and reduction
identities, *regardless of how well it fits data*. This file states the suite
as a reusable `Prop`-bundle over a measured-facts interface, so "our simulator
satisfies the suite" is a single proposition, and each field names the
falsifiable check it encodes.

The suite's tests map to this library as follows:

* Test 1 (flow balance per edge)     — `VerificationSuite.flow_balance`.
* Test 2 (work conservation)         — carried by `Accounting.conserve` inside
  `SystemFacts.acct`; the goodput bound is `VerificationSuite.goodput_bound`.
* Test 3 (Little's law per station)  — `VerificationSuite.little`.
* Test 4 (deadline budget)           — `VerificationSuite.deadline_budget`.
* Test 5 (stopping consistency)      — `VerificationSuite.stopping` and
  `VerificationSuite.tokens`.
* Test 6 (PASTA)                     — **interface-only**: the `pasta` field
  carries a caller-supplied proposition; the PASTA theorem itself is not
  formalized here, and the field exists so the claim is an explicit hypothesis
  rather than ambient folklore.
* Test 8 (truncated-geometric histogram under exogenous `p`) —
  `sum_attemptWeight` / `sum_mul_attemptWeight`
  (`Overload/Retry/Amplification.lean`).
* Test 9 (goodput plateau under zero waste) — `plateau`
  (`Overload/Capacity/Plateau.lean`).
* Test 11 (forced failure ⟹ product of caps) — `reduction_forced_failure`.
* Test 12 (degenerate knobs)         — `reduction_no_retries` (all caps 1) and
  `reduction_budget_zero` (budget `β → 0`).
* Tests 7, 10, 13–18 (base-model reduction, M/M/1 retrial match, hysteresis
  sweeps, jitter waves, latency floors, duplicate accounting, seed and
  arrival-model sensitivity, cross-level consistency) — dynamic or statistical
  checks outside this development's scope. This list is their record: they
  are named here rather than silently dropped.

**Scope honesty.** The suite's identities are per-station and per-request;
nothing here cross-links per-request attempt counts to the aggregate flow
totals ("per request *and* in aggregate" is only partially captured).
A run whose `sent`/`rate` fields are fabricated independently of its
`attempts` fields can satisfy every constraint below — ground the flow
fields in the same instrumentation as the per-request counts, or add that
linkage as an extra invariant when your request population is enumerable.

**Intent/processed dual accounting** (the signal-channel reading):
`SystemFacts` carries failure counts jointly by ground-truth *origin* and
emitted *wire code*. The suite demands both marginals match the joint
(`origin_marginal`, `wire_marginal`), so miscoding is a measurable object (the
joint matrix) rather than an untracked loss —
`Overload/Control/Observability.lean` proves why instruments built on the
wire label alone cannot see it.
-/

@[expose] public section

namespace Overload

/-- Measured facts about a running system (or a simulator run) over one
observation window: per-station flow and occupancy, bottleneck work
accounting, per-request attempt counts and deadline spend, budget-token
totals, and failure counts jointly by ground-truth origin and emitted wire
code. Everything here is observable; the `VerificationSuite` below is the
list of identities the observations must satisfy. -/
structure SystemFacts (station req origin wire : Type*) where
  /-- The stations (mechanisms, queues, tiers) under observation. -/
  stations : Finset station
  /-- The requests observed over the window. -/
  requests : Finset req
  /-- Attempts a station sends toward its downstream neighbor (window total). -/
  sent : station → ℝ
  /-- Attempts the downstream neighbor records arriving from this station. -/
  received : station → ℝ
  /-- Time-averaged in-flight occupancy at each station. -/
  inflight : station → ℝ
  /-- Mean arrival rate at each station. -/
  rate : station → ℝ
  /-- Mean sojourn time at each station. -/
  sojourn : station → ℝ
  /-- Work accounting at the bottleneck (carries `conserve : U + W + I = C·T`). -/
  acct : Accounting
  /-- Requests completed usefully within deadline, counted once, per unit time. -/
  goodput : ℝ
  /-- Offered fresh-request rate. -/
  offered : ℝ
  /-- Mean bottleneck service demand per goodput unit. -/
  sbar : ℝ
  /-- Attempts request `r` made at station `st`. -/
  attempts : req → station → ℕ
  /-- Configured attempt cap at each station. -/
  cap : station → ℕ
  /-- Total attempt sojourns plus backoff waits charged to request `r`. -/
  spent : req → ℝ
  /-- The end-to-end deadline. -/
  deadline : ℝ
  /-- Budget tokens issued over the window. -/
  issued : ℝ
  /-- Budget tokens consumed. -/
  consumed : ℝ
  /-- Budget tokens outstanding at window end. -/
  outstanding : ℝ
  /-- Budget tokens expired unused. -/
  expired : ℝ
  /-- Failure counts jointly by ground-truth origin and emitted wire code. -/
  joint : origin → wire → ℝ
  /-- Failure counts by ground-truth origin (the simulator's private truth). -/
  originCount : origin → ℝ
  /-- Failure counts by emitted wire code (what instruments see). -/
  wireCount : wire → ℝ

/-- **The verification suite**: the conservation laws and consistency
identities a run must satisfy to be trusted. `pastaFact` is the
caller-supplied sampling-unbiasedness proposition (test 6), carried as an
explicit hypothesis because the PASTA theorem is not formalized here. -/
structure VerificationSuite {station req origin wire : Type*}
    [Fintype origin] [Fintype wire] (pastaFact : Prop)
    (F : SystemFacts station req origin wire) : Prop where
  /-- Test 1: attempts leaving a station equal attempts arriving downstream.
  Failure: routing or accounting bug. -/
  flow_balance : ∀ st ∈ F.stations, F.sent st = F.received st
  /-- Test 2 (goodput side): useful work at the bottleneck covers the goodput.
  With `Accounting.conserve`, failure means capacity was manufactured. -/
  useful_work : F.goodput * F.acct.time * F.sbar ≤ F.acct.useful
  /-- Goodput never exceeds offered load (each request counted once). -/
  goodput_le_offered : F.goodput ≤ F.offered
  /-- Test 3: Little's law at every station. Failure: occupancy and latency
  bookkeeping disagree. -/
  little : ∀ st ∈ F.stations, F.inflight st = F.rate st * F.sojourn st
  /-- Test 4: no request outspends its deadline. Budget resets on reroute must
  be explicit configuration, never an accident. -/
  deadline_budget : ∀ r ∈ F.requests, F.spent r ≤ F.deadline
  /-- Test 5a: per-mechanism attempt counts never exceed caps. -/
  stopping : ∀ r ∈ F.requests, ∀ st ∈ F.stations, F.attempts r st ≤ F.cap st
  /-- Test 5b: budget tokens conserve (issued = consumed + outstanding +
  expired). -/
  tokens : F.issued = F.consumed + F.outstanding + F.expired
  /-- Dual accounting, origin marginal: origin counts match the joint. -/
  origin_marginal : ∀ o, F.originCount o = ∑ w, F.joint o w
  /-- Dual accounting, wire marginal: wire counts match the joint. -/
  wire_marginal : ∀ w, F.wireCount w = ∑ o, F.joint o w
  /-- Test 6, interface-only: the caller's sampling-unbiasedness claim. -/
  pasta : pastaFact

namespace VerificationSuite

variable {station req origin wire : Type*} [Fintype origin] [Fintype wire]
  {pastaFact : Prop} {F : SystemFacts station req origin wire}

/-- A run satisfying the suite obeys the scheme-agnostic goodput bound
`G ≤ min(λ, C/sbar)` — for every retry scheme, backoff policy, and topology,
because none appear in the hypotheses. -/
theorem goodput_bound (S : VerificationSuite pastaFact F) (hs : 0 < F.sbar) :
    F.goodput ≤ min F.offered (F.acct.capacity / F.sbar) :=
  F.acct.goodput_le hs S.useful_work S.goodput_le_offered

/-- Dual accounting is globally consistent: total failures by origin equal
total failures by wire code. A gap means failures were manufactured or lost
in translation — the accounting form of a miscoding bug. -/
theorem dual_total (S : VerificationSuite pastaFact F) :
    ∑ o, F.originCount o = ∑ w, F.wireCount w := by
  simp only [S.origin_marginal, S.wire_marginal]
  exact Finset.sum_comm

end VerificationSuite

/-!
## Closed-form reductions (tests 11 and 12)
-/

/-- **Test 11, forced failure**: if every attempt at every layer fails
(`p ≡ 1`), the expected bottom attempts per request equal exactly the product
of the caps. A simulator deviating from `∏ nᵢ` under forced failure has a
hidden cap or an unmodeled interaction — and that hidden cap is load-bearing
in every other result. -/
theorem reduction_forced_failure {ι : Type*} (s : Finset ι) (n : ι → ℕ) :
    stackAmp s (fun _ => 1) n = ∏ i ∈ s, (n i : ℝ) := by
  unfold stackAmp
  exact Finset.prod_congr rfl fun i _ =>
    (expAttempts_def 1 (n i)).trans (one_geom_sum (n i))

/-- Pin of test 11 at two layers capped `2` and `3`: forced failure drives the
stack to exactly `6` bottom attempts per request. -/
theorem reduction_forced_failure_pin :
    stackAmp (Finset.univ : Finset (Fin 2)) (fun _ => 1) ![2, 3] = 6 := by
  rw [reduction_forced_failure]
  norm_num [Fin.prod_univ_two]

/-- **Test 12, all caps 1**: with every cap at one attempt the stack does not
amplify at all — the base model with no retries, whatever the failure
probabilities. -/
theorem reduction_no_retries {ι : Type*} (s : Finset ι) (p : ι → ℝ) :
    stackAmp s p (fun _ => 1) = 1 := by
  unfold stackAmp
  simp [expAttempts_def]

/-- Pin of test 12 at unit caps: the same two layers amplify by exactly one
even at failure probabilities `1/2` and `3/4` — the caps, not the failure
levels, carry the reduction. -/
theorem reduction_no_retries_pin :
    stackAmp (Finset.univ : Finset (Fin 2)) ![1 / 2, 3 / 4] (fun _ => 1) = 1 :=
  reduction_no_retries _ _

/-- **Test 12, budget `β → 0`**: a zero retry budget (`h ≤ 1`) reproduces the
no-retries system — any offered load below the threshold leaves no congested
equilibrium. On the boundedness core, so a backpressure client (`h < 1`) is
in scope of the reduction test. -/
theorem reduction_budget_zero (L : BoundedLoop) {Θ : ℝ}
    (hβ : ∀ p ∈ Set.Icc (0 : ℝ) 1, L.h p ≤ 1) (h : L.lam < Θ) :
    ¬L.CongestedEq Θ :=
  L.clamp_no_congestedEq hβ (by simpa using h)

end Overload
