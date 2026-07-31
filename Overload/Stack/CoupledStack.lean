module

public import Overload.Basic -- shake: keep
public import Overload.Retry.Compose
public import Overload.Loop.ClosedLoop
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
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The load-coupled stack composite

`Scheme.stackToLoop` collapses a retry stack to its constant worst-case
amplification — sound for clamp certificates, structurally incapable of
bistability. This file builds the composite that V1 deferred: a stack whose
amplification **responds to the bottom failure level**, finally consuming
`Compose.composeFail`.

Entries are own-cap pairs `(ℓᵢ, nᵢ)` — a layer's local failure probability
and its *own* retry cap — deliberately bare pairs rather than proof-carrying
`Layer` records. The recursion applies the retry power on invocation exit:

* `invokeFail layers p` — the probability that one full invocation of the
  stack (all internal retries included) fails, over raw bottom per-attempt
  failure `p`. Per cons: one attempt fails per `composeFail ℓ · 1` against
  the sublist's invocation, and the invocation fails iff all `n` attempts
  fail.
* `coupledAmp layers p` — expected bottom attempts per top-level request:
  the head retries against the composed failure below it, and each head
  attempt spawns one full invocation of the sublist. The product across
  layers is the per-layer Wald modeling assumption (same status as
  `stackAmp`; `Composition.lean`'s branching-Wald section is its finite
  honest core). Locally-failing attempts are charged a full downstream
  invocation — the worst case; fail-fast refinements only reduce it.

`coupledLoop` assembles the composite into a `ClosedLoop` over an arbitrary
kernel `g` — the binding resource may be a serving fleet or an intermediate
hop's memory or bandwidth, denominated in attempts against it. Because the
response is genuinely load-coupled, both phase directions are expressible:
`coupled_budget_no_congestedEq` certifies collapse-freedom with one product
inequality, and `coupled_two_layer_bistable` exhibits a bistable two-layer
composite over the step kernel. `composeFail`'s exponent is the cap of the
layer *below*; the recursions here pair each layer with its own cap
instead — the pairing that makes the inductions clean.
-/

@[expose] public section

namespace Overload

/-- Product of the caps of an own-cap layer list, as a real: the
forced-failure envelope of the stack. -/
def capProd (layers : List (ℝ × ℕ)) : ℝ :=
  (layers.map fun x => (x.2 : ℝ)).prod

/-- The empty stack's cap product is `1`. -/
@[simp] theorem capProd_nil : capProd [] = 1 := rfl

/-- The cap product of a cons: the head's cap times the tail's cap
product. -/
@[simp] theorem capProd_cons (x : ℝ × ℕ) (rest : List (ℝ × ℕ)) :
    capProd (x :: rest) = (x.2 : ℝ) * capProd rest := by
  simp [capProd]

/-- Failure probability of one full invocation of the stack (every layer's
internal retries included) over raw bottom per-attempt failure `p`. -/
def invokeFail : List (ℝ × ℕ) → ℝ → ℝ
  | [], p => p
  | (ℓ, n) :: rest, p => (composeFail ℓ (invokeFail rest p) 1) ^ n

/-- The empty stack's invocation failure is the raw bottom per-attempt
failure `p`. -/
@[simp] theorem invokeFail_nil (p : ℝ) : invokeFail [] p = p := rfl

/-- The invocation failure of a cons: the head's per-attempt failure
`composeFail ℓ (invokeFail rest p) 1`, raised to its cap `n`. -/
@[simp] theorem invokeFail_cons (ℓ : ℝ) (n : ℕ) (rest : List (ℝ × ℕ))
    (p : ℝ) :
    invokeFail ((ℓ, n) :: rest) p
      = (composeFail ℓ (invokeFail rest p) 1) ^ n := rfl

/-- Expected bottom attempts per top-level request, as a function of the raw
bottom failure `p` — the load-coupled amplification response of the stack. -/
def coupledAmp : List (ℝ × ℕ) → ℝ → ℝ
  | [], _ => 1
  | (ℓ, n) :: rest, p =>
      expAttempts (composeFail ℓ (invokeFail rest p) 1) n * coupledAmp rest p

/-- The empty stack's load-coupled amplification is `1`: one bottom attempt
per top-level request. -/
@[simp] theorem coupledAmp_nil (p : ℝ) : coupledAmp [] p = 1 := rfl

/-- The load-coupled amplification of a cons: the head's expected attempts
against the composed failure below it, times the load-coupled amplification
of the tail. -/
@[simp] theorem coupledAmp_cons (ℓ : ℝ) (n : ℕ) (rest : List (ℝ × ℕ))
    (p : ℝ) :
    coupledAmp ((ℓ, n) :: rest) p
      = expAttempts (composeFail ℓ (invokeFail rest p) 1) n
          * coupledAmp rest p := rfl

/-- Failure probabilities stay probabilities through the whole stack. -/
theorem invokeFail_mem_Icc (layers : List (ℝ × ℕ)) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1) :
    invokeFail layers p ∈ Set.Icc (0 : ℝ) 1 := by
  induction layers with
  | nil => simpa using hp
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    obtain ⟨hhd, hℓtl⟩ := List.forall_mem_cons.mp hℓ
    have htl : invokeFail tl p ∈ Set.Icc (0 : ℝ) 1 := ih hℓtl
    have hc := composeFail_mem_Icc hhd htl 1
    exact ⟨pow_nonneg hc.1 n, pow_le_one₀ hc.1 hc.2⟩

/-- A worse bottom raises the invocation failure of the whole stack. -/
theorem invokeFail_mono_base (layers : List (ℝ × ℕ)) {p q : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hpq : p ≤ q)
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1) :
    invokeFail layers p ≤ invokeFail layers q := by
  induction layers with
  | nil => simpa using hpq
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    obtain ⟨hhd, hℓtl⟩ := List.forall_mem_cons.mp hℓ
    have htl : invokeFail tl p ∈ Set.Icc (0 : ℝ) 1 :=
      invokeFail_mem_Icc tl hp hℓtl
    have hrec : invokeFail tl p ≤ invokeFail tl q := ih hℓtl
    have hc : composeFail ℓ (invokeFail tl p) 1
        ≤ composeFail ℓ (invokeFail tl q) 1 :=
      composeFail_mono_down hhd.2 htl.1 hrec 1
    have hc0 : 0 ≤ composeFail ℓ (invokeFail tl p) 1 :=
      (composeFail_mem_Icc hhd htl 1).1
    exact pow_le_pow_left₀ hc0 hc n

/-- Under total bottom failure the whole stack fails surely — hypothesis
free. -/
theorem invokeFail_at_one (layers : List (ℝ × ℕ)) :
    invokeFail layers 1 = 1 := by
  induction layers with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    rw [invokeFail_cons, ih]
    simp [composeFail]

/-- The load-coupled amplification is nonnegative: each per-layer factor
is. -/
theorem coupledAmp_nonneg (layers : List (ℝ × ℕ)) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ coupledAmp layers p := by
  induction layers with
  | nil => norm_num
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    obtain ⟨hhd, hℓtl⟩ := List.forall_mem_cons.mp hℓ
    have htl : invokeFail tl p ∈ Set.Icc (0 : ℝ) 1 :=
      invokeFail_mem_Icc tl hp hℓtl
    have hc := composeFail_mem_Icc hhd htl 1
    have hrec : 0 ≤ coupledAmp tl p := ih hℓtl
    exact mul_nonneg (expAttempts_nonneg hc.1 n) hrec

/-- The load-coupled amplification is at least `1` once every layer's cap
is. -/
theorem one_le_coupledAmp (layers : List (ℝ × ℕ)) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1)
    (hcap : ∀ x ∈ layers, 1 ≤ x.2) : 1 ≤ coupledAmp layers p := by
  induction layers with
  | nil => norm_num
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    obtain ⟨hhd, hℓtl⟩ := List.forall_mem_cons.mp hℓ
    obtain ⟨hcaphd, hcaptl⟩ := List.forall_mem_cons.mp hcap
    have htl : invokeFail tl p ∈ Set.Icc (0 : ℝ) 1 :=
      invokeFail_mem_Icc tl hp hℓtl
    have hc := composeFail_mem_Icc hhd htl 1
    have hhead : 1 ≤ expAttempts (composeFail ℓ (invokeFail tl p) 1) n :=
      one_le_expAttempts hc.1 hcaphd
    have hrec : 1 ≤ coupledAmp tl p := ih hℓtl hcaptl
    rw [coupledAmp_cons]
    exact hhead.trans (le_mul_of_one_le_right (zero_le_one.trans hhead) hrec)

/-- The load-coupled amplification never exceeds the cap product, the
forced-failure envelope of the stack. -/
theorem coupledAmp_le_capProd (layers : List (ℝ × ℕ)) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1) :
    coupledAmp layers p ≤ capProd layers := by
  induction layers with
  | nil => norm_num
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    obtain ⟨hhd, hℓtl⟩ := List.forall_mem_cons.mp hℓ
    have htl : invokeFail tl p ∈ Set.Icc (0 : ℝ) 1 :=
      invokeFail_mem_Icc tl hp hℓtl
    have hc := composeFail_mem_Icc hhd htl 1
    have hhead : expAttempts (composeFail ℓ (invokeFail tl p) 1) n ≤ n :=
      expAttempts_le_cap hc.1 hc.2 n
    have hrec : coupledAmp tl p ≤ capProd tl := ih hℓtl
    have hrecnn : 0 ≤ coupledAmp tl p := coupledAmp_nonneg tl hp hℓtl
    rw [coupledAmp_cons, capProd_cons]
    exact mul_le_mul hhead hrec hrecnn (Nat.cast_nonneg n)

/-- **The load-coupled monotonicity**: a worse bottom raises the whole
stack's amplification. This is the field the constant envelope cannot
provide, and what makes bistability expressible for composites. -/
theorem coupledAmp_mono_base (layers : List (ℝ × ℕ)) {p q : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) (hpq : p ≤ q)
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1) :
    coupledAmp layers p ≤ coupledAmp layers q := by
  induction layers with
  | nil => norm_num
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    obtain ⟨hhd, hℓtl⟩ := List.forall_mem_cons.mp hℓ
    have htlp : invokeFail tl p ∈ Set.Icc (0 : ℝ) 1 :=
      invokeFail_mem_Icc tl hp hℓtl
    have htlq : invokeFail tl q ∈ Set.Icc (0 : ℝ) 1 :=
      invokeFail_mem_Icc tl hq hℓtl
    have hcp := composeFail_mem_Icc hhd htlp 1
    have hcq := composeFail_mem_Icc hhd htlq 1
    have hfail : composeFail ℓ (invokeFail tl p) 1
        ≤ composeFail ℓ (invokeFail tl q) 1 :=
      composeFail_mono_down hhd.2 htlp.1
        (invokeFail_mono_base tl hp hpq hℓtl) 1
    have hhead : expAttempts (composeFail ℓ (invokeFail tl p) 1) n
        ≤ expAttempts (composeFail ℓ (invokeFail tl q) 1) n :=
      expAttempts_mono_left hcp.1 hfail n
    have hrec : coupledAmp tl p ≤ coupledAmp tl q := ih hℓtl
    have hrecnn : 0 ≤ coupledAmp tl p := coupledAmp_nonneg tl hp hℓtl
    have hheadnnq : 0 ≤ expAttempts (composeFail ℓ (invokeFail tl q) 1) n :=
      expAttempts_nonneg hcq.1 n
    rw [coupledAmp_cons, coupledAmp_cons]
    exact mul_le_mul hhead hrec hrecnn hheadnnq

/-- **Saturation** — hypothesis free: at total bottom failure every layer
burns its whole cap and the composite equals the forced-failure envelope
`∏ nᵢ`. The load-coupled refinement of
`reduction_forced_failure`. -/
theorem coupledAmp_at_one (layers : List (ℝ × ℕ)) :
    coupledAmp layers 1 = capProd layers := by
  induction layers with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨ℓ, n⟩ := hd
    rw [coupledAmp_cons, capProd_cons, ih, invokeFail_at_one]
    have h : composeFail ℓ 1 1 = 1 := by simp [composeFail]
    rw [h, expAttempts_def, one_geom_sum]

/-- **The code ↔ architecture composition, load-coupled form.** A whole
stack of retry layers over an arbitrary kernel `g` — the binding resource
may be a serving fleet or an intermediate hop's memory or bandwidth,
denominated in attempts against it — assembles into a `ClosedLoop` whose
amplification response genuinely depends on the failure level. Both phase
directions now apply: the clamp side (`coupled_budget_no_congestedEq`) and
the band (`coupled_two_layer_bistable`). -/
noncomputable def coupledLoop (lam : ℝ) (g : ℝ → ℝ)
    (layers : List (ℝ × ℕ)) (hlam : 0 ≤ lam)
    (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)))
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1)
    (hcap : ∀ x ∈ layers, 1 ≤ x.2) : ClosedLoop where
  lam := lam
  g := g
  h := fun q => coupledAmp layers q
  Amax := capProd layers
  lam_nonneg := hlam
  g_mem := hg_mem
  g_mono := hg_mono
  h_mono := fun _p hp _q hq hpq => coupledAmp_mono_base layers hp hq hpq hℓ
  h_one_le := fun _p hp => one_le_coupledAmp layers hp hℓ hcap
  h_le_Amax := fun _p hp => coupledAmp_le_capProd layers hp hℓ

/-- **One product inequality certifies the load-coupled stack**: offered
load times the cap product below the threshold removes every congested
equilibrium of the composite, for every kernel. -/
theorem coupled_budget_no_congestedEq (lam : ℝ) (g : ℝ → ℝ)
    (layers : List (ℝ × ℕ)) (hlam : 0 ≤ lam)
    (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)))
    (hℓ : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1)
    (hcap : ∀ x ∈ layers, 1 ≤ x.2) {C : ℝ}
    (hbudget : lam * capProd layers < C) :
    ¬(coupledLoop lam g layers hlam hg_mem hg_mono hℓ hcap).CongestedEq C :=
  (coupledLoop lam g layers hlam hg_mem hg_mono hℓ hcap).clamp_no_congestedEq
    (fun _p hp => coupledAmp_le_capProd layers hp hℓ) hbudget

/-!
## The two-layer bistable composite

Layers `[(1/2, 2), (1/2, 2)]` over `stepKernel 24` at offered load `8`.
Healthy side (`p = 0`): the inner layer's invocation fails with probability
`(1/2)² = 1/4`, the head's per-attempt failure is
`composeFail (1/2) (1/4) 1 = 5/8`, and the composite amplification is
`(1 + 5/8)·(1 + 1/2) = 39/16`, so `F(39/2) = 8·39/16 = 39/2` — an exact
fixed point strictly below capacity, with genuinely load-coupled healthy
amplification (`39/16 > 1`, not the trivial envelope). Congested side:
`F(24) = 8·capProd = 32 ≥ 24`.
-/

/-- Numeric regression: the healthy-side composite amplification is
`39/16`. -/
theorem coupledAmp_twoLayer_zero :
    coupledAmp [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)] 0 = 39/16 := by
  norm_num [coupledAmp_cons, coupledAmp_nil, invokeFail_cons, invokeFail_nil,
    composeFail, expAttempts_def]

/-- Membership bundle for the concrete two-layer stack. -/
theorem twoLayer_mem :
    ∀ x ∈ [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)], x.1 ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [List.forall_mem_cons, Set.mem_Icc]

/-- Cap bundle for the concrete two-layer stack. -/
theorem twoLayer_cap :
    ∀ x ∈ [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)], 1 ≤ x.2 := by
  norm_num [List.forall_mem_cons]

/-- The concrete two-layer composite: layers `[(1/2, 2), (1/2, 2)]` over
`stepKernel 24` at offered load `8`. -/
noncomputable abbrev twoLayerLoop : ClosedLoop :=
  coupledLoop 8 (stepKernel 24) [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)]
    (by norm_num) (stepKernel_mem 24) (stepKernel_monoOn 24)
    twoLayer_mem twoLayer_cap

/-- The congested-side inflow at saturation, shared by the bistability and
equilibrium certificates: `F(24) = 8·capProd = 32 ≥ 24`. -/
theorem twoLayer_inflow : (24 : ℝ) ≤ twoLayerLoop.F 24 := by
  change (24 : ℝ) ≤ 8 * coupledAmp [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)]
    (stepKernel 24 24)
  rw [stepKernel_of_ge (by norm_num), coupledAmp_at_one]
  norm_num [capProd_cons, capProd_nil]

/-- **A bistable load-coupled composite.** The two-layer stack over the step
kernel holds a healthy equilibrium at `39/2 < 24` (an exact fixed point,
with real amplification) and a congested state at `24` — the band
`39/2 < 24 ≤ 32`, certified by two point evaluations. This is the theorem
the constant-envelope `stackToLoop` structurally cannot state. -/
theorem coupled_two_layer_bistable : BistableOn twoLayerLoop.F 0 32 := by
  refine twoLayerLoop.bistableOn_of_two_points (x := 39/2) (y := 24)
    (by norm_num) ?_ twoLayer_inflow (by norm_num) ?_
  · change (8 : ℝ) * coupledAmp [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)]
      (stepKernel 24 (39/2)) ≤ 39/2
    rw [stepKernel_of_lt (by norm_num)]
    norm_num [coupledAmp_cons, coupledAmp_nil, invokeFail_cons,
      invokeFail_nil, composeFail, expAttempts_def]
  · change (8 : ℝ) * capProd [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)] ≤ 32
    norm_num [capProd_cons, capProd_nil]

/-- The congested state of the two-layer composite is a genuine
equilibrium — a fixed point at or above `24` (here `F(32) = 32`) — by the
inflow certificate. -/
theorem coupled_two_layer_congestedEq : twoLayerLoop.CongestedEq 24 :=
  twoLayerLoop.congestedEq_of_inflow (by norm_num) twoLayer_inflow

/-- Numeric regression on the budget certificate, the same two layers at a
lighter load: `5 · 4 = 20` under a threshold of `21` removes every congested
equilibrium — one product inequality, no evaluation of the composite. -/
theorem coupled_budget_no_congestedEq_at_five :
    ¬(coupledLoop 5 (stepKernel 24) [((1/2 : ℝ), 2), ((1/2 : ℝ), 2)]
      (by norm_num) (stepKernel_mem 24) (stepKernel_monoOn 24) twoLayer_mem
      twoLayer_cap).CongestedEq 21 :=
  coupled_budget_no_congestedEq 5 _ _ (by norm_num) (stepKernel_mem 24)
    (stepKernel_monoOn 24) twoLayer_mem twoLayer_cap
    (by norm_num [capProd_cons, capProd_nil])

end Overload
