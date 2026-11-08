import KT.Defs

/-! # D4: `prefixedClosure` as a `ClosureOperator` -/

open Function (IsFixedPt)
open Set

namespace KT

section General

variable {α : Type*} [ConditionallyCompleteLattice α] {f g : α → α} {x : α}
  (hf : Monotone f) (hbdd : BddAbove (range f))

@[simp] theorem prefixedClosure_apply (x : α) :
    prefixedClosure f hf hbdd x = sInf {y | x ≤ y ∧ f y ≤ y} := rfl

/-- Definitional agreement with D2 (Route 4). -/
theorem prefixedClosure_eq_nextFixedPt (x : α) :
    prefixedClosure f hf hbdd x = nextFixedPt f x := rfl

theorem prefixedClosure_isClosed_iff : (prefixedClosure f hf hbdd).IsClosed x ↔ f x ≤ x :=
  Iff.rfl

theorem isFixedPt_prefixedClosure (hx : x ≤ f x) : IsFixedPt f (prefixedClosure f hf hbdd x) := by
  set c := prefixedClosure f hf hbdd
  have h₁ : f (c x) ≤ c x := c.isClosed_closure x
  have h₂ : c x ≤ f (c x) := c.closure_min (hx.trans (hf (c.le_closure x))) (hf h₁)
  exact h₁.antisymm h₂

/-- The one conditionally-complete Knaster–Tarski statement. -/
theorem isLeast_prefixedClosure (hx : x ≤ f x) :
    IsLeast {y | x ≤ y ∧ IsFixedPt f y} (prefixedClosure f hf hbdd x) :=
  ⟨⟨(prefixedClosure f hf hbdd).le_closure x, isFixedPt_prefixedClosure hf hbdd hx⟩,
    fun _ hy ↦ (prefixedClosure f hf hbdd).closure_min hy.1 hy.2.le⟩

theorem iterate_le_prefixedClosure (hx : x ≤ f x) (n : ℕ) :
    f^[n] x ≤ prefixedClosure f hf hbdd x := by
  induction n with
  | zero => exact (prefixedClosure f hf hbdd).le_closure x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hf ih).trans_eq (isFixedPt_prefixedClosure hf hbdd hx).eq

theorem prefixedClosure_le_prefixedClosure (hg : Monotone g) (hbg : BddAbove (range g))
    (hfg : ∀ y, f y ≤ g y) (x : α) :
    prefixedClosure f hf hbdd x ≤ prefixedClosure g hg hbg x :=
  csInf_le_csInf ⟨x, fun _ h ↦ h.1⟩ (prefixed_nonempty hbg x) fun _ hy ↦ ⟨hy.1, (hfg _).trans hy.2⟩

/-- The dual: closure operator on `αᵒᵈ` whose closed elements are the postfixed points. -/
noncomputable def postfixedKernel (f : α → α) (hf : Monotone f) (hbdd : BddBelow (range f)) :
    ClosureOperator αᵒᵈ :=
  prefixedClosure (α := αᵒᵈ) (fun x ↦ OrderDual.toDual (f (OrderDual.ofDual x))) hf.dual hbdd

theorem postfixedKernel_apply (hbdd' : BddBelow (range f)) (x : α) :
    OrderDual.ofDual (postfixedKernel f hf hbdd' (OrderDual.toDual x)) = prevFixedPt f x := rfl

end General

section Bridge

variable {β : Type*} [CompleteLattice β]

theorem bddAbove_range_of_completeLattice (f : β → β) : BddAbove (range f) :=
  ⟨⊤, fun _ _ ↦ le_top⟩

/-- On a complete lattice, `prefixedClosure` is `ClosureOperator.ofCompletePred` for the
prefixed-point predicate. -/
theorem _root_.OrderHom.prefixedClosure_eq (f : β →o β) :
    prefixedClosure f f.mono (bddAbove_range_of_completeLattice f) =
      ClosureOperator.ofCompletePred (fun y ↦ f y ≤ y)
        (fun _ hs ↦ le_sInf fun y hy ↦ (f.mono (sInf_le hy)).trans (hs y hy)) :=
  ClosureOperator.ext_isClosed _ _ fun _ ↦ Iff.rfl

/-- On a complete lattice, `OrderHom.nextFixed` is `prefixedClosure`. -/
theorem _root_.OrderHom.coe_nextFixed_eq_prefixedClosure (f : β →o β) {x : β} (hx : x ≤ f x) :
    (f.nextFixed x hx : β) = prefixedClosure f f.mono (bddAbove_range_of_completeLattice f) x := by
  change sInf {y | (OrderHom.const β x ⊔ f) y ≤ y} = sInf {y | x ≤ y ∧ f y ≤ y}
  congr 1
  ext y
  exact sup_le_iff

end Bridge

end KT
