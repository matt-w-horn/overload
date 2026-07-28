import Mathlib
import Overload.Amplification
import Overload.Deadline
import Overload.Bistability
import Overload.Composition

/-!
# Retry schemes and the code ↔ architecture composition theorem

The scheme-agnostic formalism: a retry scheme at any point
in the stack is a tuple `(trigger, stop, timing, scope)`. Its quantitative
content, for everything downstream, is a single number — the amplification it
contributes — obtained by feeding its timing rule through the deadline
arithmetic (`Deadline.neff`) to a cap, then through the truncated-geometric
mean (`Amplification.expAttempts`).

The payoff of this file is `stackToLoop`: a whole stack of schemes composes
multiplicatively into a single amplification number `layersAmp S`, and the
resulting **constant-response loop** is again a monotone bounded demand
operator (`Bistability.ClosedLoop`). This is the *worst-case envelope*
composite: its response ignores the failure level, so the clamp-side theorems
apply verbatim (`stack_budget_no_congestedEq` certifies the whole
architecture with one product inequality, for every kernel — in min-plus
network-calculus language, `λ·∏capᵢ < C` is an arrival-curve statement:
the retry stack's worst-case output envelope stays under the service
capacity), while
bistability — which needs a load-*coupled* response — cannot arise in this
composite by construction. The load-coupled composite lives in
`Overload/CoupledStack.lean` (`coupledLoop`): failure composition fed
through `expAttempts` into a non-constant response, where both phase
directions are expressible. Code-level retry loops and the architecture
remain one object at different scales: monotone bounded parts compose into
a monotone bounded demand operator.
-/

namespace Overload

/-- A retry layer's quantitative signature: an i.i.d. per-attempt failure
probability and the deadline-capped attempt count it is allowed. (The trigger
and scope rules of the full scheme tuple enter through which failures are
eligible — folded into `p` — and which resource is charged; the timing and
stopping rules enter through `cap`, computed upstream by `Deadline.neff`.) -/
structure Layer where
  /-- Per-attempt failure probability of retry-eligible outcomes at this
  layer. -/
  p : ℝ
  /-- Deadline-capped attempt count allowed at this layer (from
  `Deadline.neff`). -/
  cap : ℕ
  p_mem : p ∈ Set.Icc (0 : ℝ) 1
  cap_pos : 1 ≤ cap

/-- The amplification a single layer contributes. -/
def Layer.amp (ℓ : Layer) : ℝ := expAttempts ℓ.p ℓ.cap

theorem Layer.one_le_amp (ℓ : Layer) : 1 ≤ ℓ.amp :=
  one_le_expAttempts ℓ.p_mem.1 ℓ.cap_pos

theorem Layer.amp_pos (ℓ : Layer) : 0 < ℓ.amp :=
  lt_of_lt_of_le zero_lt_one ℓ.one_le_amp

theorem Layer.amp_le_cap (ℓ : Layer) : ℓ.amp ≤ ℓ.cap :=
  expAttempts_le_cap ℓ.p_mem.1 ℓ.p_mem.2 ℓ.cap

/-- The composite amplification of a stack of retry layers (top of the call
tree first): the product of the layers' amplifications — the multiplicative
composition assumed by the modeling definition `stackAmp`
(`Overload/Composition.lean`), here in list form for ordered stacks. -/
def layersAmp (S : List Layer) : ℝ := (S.map Layer.amp).prod

@[simp] theorem layersAmp_nil : layersAmp [] = 1 := rfl

@[simp] theorem layersAmp_cons (ℓ : Layer) (S : List Layer) :
    layersAmp (ℓ :: S) = ℓ.amp * layersAmp S := by
  simp [layersAmp]

theorem one_le_layersAmp (S : List Layer) : 1 ≤ layersAmp S := by
  induction S with
  | nil => simp
  | cons ℓ S ih =>
    rw [layersAmp_cons]
    exact ℓ.one_le_amp.trans (le_mul_of_one_le_right ℓ.amp_pos.le ih)

theorem layersAmp_pos (S : List Layer) : 0 < layersAmp S :=
  lt_of_lt_of_le zero_lt_one (one_le_layersAmp S)

/-- The composite amplification is bounded by the product of the caps — the
forced-failure envelope: if every attempt at every layer fails, the request
makes exactly `∏ capᵢ` bottom attempts. -/
theorem layersAmp_le_prod_cap (S : List Layer) :
    layersAmp S ≤ (S.map (fun ℓ => (ℓ.cap : ℝ))).prod := by
  induction S with
  | nil => simp
  | cons ℓ S ih =>
    rw [layersAmp_cons, List.map_cons, List.prod_cons]
    exact mul_le_mul ℓ.amp_le_cap ih (layersAmp_pos S).le (Nat.cast_nonneg _)

/-- **The code ↔ architecture composition, worst-case form.** A whole stack
of retry schemes assembles into a single `ClosedLoop` whose amplification
response is the *constant* composite `layersAmp S` — the product of the
per-layer amplifications, i.e. the saturated worst case. The clamp-side
theorems (`clamp_no_congestedEq` and its corollaries) apply verbatim, and
because the response is constant the resulting `F` is constant in `Λ`
(`stackToLoop_F`). Read this composite on the clamp side only: bistability
needs a load-coupled response (see the module docstring), but nothing here
*proves* this constructor cannot be bistable —
`ClosedLoop.not_bistableOn_of_const` rules that out for a constant kernel
`g`, which is a different hypothesis. The load-coupled composite is
`coupledLoop` in `CoupledStack.lean`. -/
noncomputable def stackToLoop (S : List Layer) (lam : ℝ) (g : ℝ → ℝ)
    (hlam : 0 ≤ lam) (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))) : ClosedLoop where
  lam := lam
  g := g
  h := fun _ => layersAmp S
  Amax := layersAmp S
  lam_nonneg := hlam
  g_mem := hg_mem
  g_mono := hg_mono
  h_mono := monotoneOn_const
  h_one_le := fun _ _ => one_le_layersAmp S
  h_le_Amax := fun _ _ => le_refl _

/-- The composite loop's demand operator is exactly `Λ ↦ lam · layersAmp S`
(constant amplification): the stack acts as one aggregate multiplier. -/
theorem stackToLoop_F (S : List Layer) (lam : ℝ) (g : ℝ → ℝ) (hlam : 0 ≤ lam)
    (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ))) (Λ : ℝ) :
    (stackToLoop S lam g hlam hg_mem hg_mono).F Λ = lam * layersAmp S := rfl

/-- **A budget on the whole architecture.** If the composite stack
amplification `layersAmp S` times the offered rate is below capacity, the
assembled loop has no congested equilibrium — one inequality on the product
certifies the entire multi-layer system collapse-free. -/
theorem stack_budget_no_congestedEq (S : List Layer) {lam C : ℝ} (g : ℝ → ℝ)
    (hlam : 0 ≤ lam) (hg_mem : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)))
    (hbudget : lam * layersAmp S < C) :
    ¬(stackToLoop S lam g hlam hg_mem hg_mono).CongestedEq C :=
  (stackToLoop S lam g hlam hg_mem hg_mono).clamp_no_congestedEq
    (K := layersAmp S) (fun _ _ => le_refl _) hbudget

/-- Numeric regression on the constant response: one layer failing half its
attempts at cap `2` contributes `3/2`, so at offered load `2` the composite's
demand operator sits at `3` — below the kernel's step at `10` and above it
alike. That is what the worst-case envelope costs: no load coupling left. -/
theorem stackToLoop_F_at_demo :
    (stackToLoop [⟨1 / 2, 2, by norm_num, by norm_num⟩] 2 (stepKernel 10)
      (by norm_num) (stepKernel_mem 10) (stepKernel_monoOn 10)).F 5 = 3 ∧
    (stackToLoop [⟨1 / 2, 2, by norm_num, by norm_num⟩] 2 (stepKernel 10)
      (by norm_num) (stepKernel_mem 10) (stepKernel_monoOn 10)).F 100 = 3 := by
  constructor <;>
    · rw [stackToLoop_F]
      norm_num [layersAmp_cons, layersAmp_nil, Layer.amp, expAttempts_def]

end Overload
