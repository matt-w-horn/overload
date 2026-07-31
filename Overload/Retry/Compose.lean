module

public import Overload.Basic -- shake: keep
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Downward failure composition across layers

Per-attempt failure composes downward through a stack: a parent
attempt at layer `i` fails iff it fails locally (probability `ℓᵢ`) or —
surviving locally — its downstream call still fails after all of the next
layer's retries (probability `fᵢ₊₁^{nᵢ₊₁}`):

`fᵢ = 1 - (1 - ℓᵢ)(1 - fᵢ₊₁^{nᵢ₊₁})`.

The retry cap in the exponent belongs to the layer *below*, so the stack is a
list of pairs `(ℓᵢ, nᵢ₊₁)` folded over a base failure probability — the
reference presentation, kept as stated. `Overload/Stack/CoupledStack.lean`
consumes the one-layer `composeFail` (with its `Icc` and monotonicity
lemmas), building its own recursions over own-cap pairs `(ℓᵢ, nᵢ)` (the
power applied on invocation exit) — the shape that makes the amplification
inductions clean. The `stackFail` fold itself has no downstream consumers and stays as
the reference presentation.
-/

@[expose] public section

namespace Overload

/-- One-layer downward failure composition. -/
def composeFail (ℓ f : ℝ) (m : ℕ) : ℝ := 1 - (1 - ℓ) * (1 - f ^ m)

/-- Failure probabilities stay probabilities through one layer. -/
theorem composeFail_mem_Icc {ℓ f : ℝ} (hℓ : ℓ ∈ Set.Icc (0 : ℝ) 1)
    (hf : f ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    composeFail ℓ f m ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hℓ0, hℓ1⟩ := hℓ
  obtain ⟨hf0, hf1⟩ := hf
  have hm0 : 0 ≤ f ^ m := pow_nonneg hf0 m
  have hm1 : f ^ m ≤ 1 := pow_le_one₀ hf0 hf1
  unfold composeFail
  constructor
  · nlinarith
  · nlinarith

/-- More downstream failure means more composed failure. -/
theorem composeFail_mono_down {ℓ f f' : ℝ} (hℓ1 : ℓ ≤ 1) (hf0 : 0 ≤ f)
    (h : f ≤ f') (m : ℕ) : composeFail ℓ f m ≤ composeFail ℓ f' m := by
  have hp : f ^ m ≤ f' ^ m := pow_le_pow_left₀ hf0 h m
  unfold composeFail
  nlinarith

/-- More downstream retries (a larger cap on the layer below) *reduce* the
failure probability visible from above — the sense in which retries mask. -/
theorem composeFail_antitone_cap {ℓ f : ℝ} (hℓ1 : ℓ ≤ 1) (hf0 : 0 ≤ f)
    (hf1 : f ≤ 1) {m m' : ℕ} (h : m ≤ m') :
    composeFail ℓ f m' ≤ composeFail ℓ f m := by
  have hp : f ^ m' ≤ f ^ m := pow_le_pow_of_le_one hf0 hf1 h
  unfold composeFail
  nlinarith

/-- Pin of the masking direction, with both values: over a bottom layer that
fails half its attempts, raising the downstream cap from one to two drops the
composed failure from `3/4` to `5/8`. -/
theorem composeFail_antitone_cap_pin :
    composeFail (1 / 2) (1 / 2) 2 ≤ composeFail (1 / 2) (1 / 2) 1 ∧
      composeFail (1 / 2) (1 / 2) 2 = 5 / 8 ∧
      composeFail (1 / 2) (1 / 2) 1 = 3 / 4 :=
  ⟨composeFail_antitone_cap (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    by norm_num [composeFail], by norm_num [composeFail]⟩

/-- A layered stack, top-down: each element `(ℓᵢ, nᵢ₊₁)` pairs layer `i`'s
local failure probability with the retry cap applied to the next layer down,
folded over the bottom layer's failure probability. -/
def stackFail : List (ℝ × ℕ) → ℝ → ℝ
  | [], base => base
  | (ℓ, m) :: rest, base => composeFail ℓ (stackFail rest base) m

/-- The empty stack leaves the base failure probability unchanged. -/
@[simp] theorem stackFail_nil (base : ℝ) : stackFail [] base = base := rfl

/-- Prepending a layer is one-layer downward composition over the rest of
the stack. -/
@[simp] theorem stackFail_cons (ℓ : ℝ) (m : ℕ) (rest : List (ℝ × ℕ))
    (base : ℝ) :
    stackFail ((ℓ, m) :: rest) base = composeFail ℓ (stackFail rest base) m :=
  rfl

/-- Failure probabilities stay probabilities through the stack. -/
theorem stackFail_mem_Icc (layers : List (ℝ × ℕ)) {base : ℝ}
    (hbase : base ∈ Set.Icc (0 : ℝ) 1)
    (hlayers : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1) :
    stackFail layers base ∈ Set.Icc (0 : ℝ) 1 := by
  induction layers with
  | nil => simpa using hbase
  | cons hd tl ih =>
    obtain ⟨ℓ, m⟩ := hd
    obtain ⟨hℓ, htl'⟩ := List.forall_mem_cons.mp hlayers
    have htl : stackFail tl base ∈ Set.Icc (0 : ℝ) 1 := ih htl'
    simpa using composeFail_mem_Icc hℓ htl m

/-- The stack is monotone in the bottom layer's failure probability: worse
bottom conditions are visible (weakly) all the way up. -/
theorem stackFail_mono_base (layers : List (ℝ × ℕ)) {b b' : ℝ}
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (h : b ≤ b')
    (hlayers : ∀ x ∈ layers, x.1 ∈ Set.Icc (0 : ℝ) 1) :
    stackFail layers b ≤ stackFail layers b' := by
  induction layers with
  | nil => simpa using h
  | cons hd tl ih =>
    obtain ⟨ℓ, m⟩ := hd
    obtain ⟨hℓ, htl'⟩ := List.forall_mem_cons.mp hlayers
    have htl : stackFail tl b ∈ Set.Icc (0 : ℝ) 1 :=
      stackFail_mem_Icc tl hb htl'
    have hrec : stackFail tl b ≤ stackFail tl b' := ih htl'
    simpa using composeFail_mono_down hℓ.2 htl.1 hrec m

/-- Pin of bottom-layer monotonicity through one layer of local failure `1/2`
at a unit downstream cap: a bottom that never fails shows `1/2` at the top, a
bottom that always fails shows `1`. -/
theorem stackFail_mono_base_pin :
    stackFail [(1 / 2, 1)] 0 ≤ stackFail [(1 / 2, 1)] 1 ∧
      stackFail [(1 / 2, 1)] 0 = 1 / 2 ∧ stackFail [(1 / 2, 1)] 1 = 1 :=
  ⟨stackFail_mono_base _ ⟨le_rfl, zero_le_one⟩ zero_le_one (by norm_num),
    by rw [stackFail_cons, stackFail_nil]; norm_num [composeFail],
    by rw [stackFail_cons, stackFail_nil]; norm_num [composeFail]⟩

end Overload
