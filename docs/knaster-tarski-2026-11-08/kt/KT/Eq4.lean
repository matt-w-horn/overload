import KT.Defs

/-! # Route 4 (definitional): D4 = D2 by `rfl`; `OrderHom.nextFixed` = D2 by unfolding.
Independent of every other route (imports only `KT.Defs`). -/

namespace KT

variable {α : Type*} [ConditionallyCompleteLattice α] {f : α → α}

theorem route4_prefixedClosure_eq_nextFixedPt (hf : Monotone f) (hbdd : BddAbove (Set.range f))
    (x : α) : prefixedClosure f hf hbdd x = nextFixedPt f x := rfl

theorem route4_nextFixed_eq_nextFixedPt {β : Type*} [CompleteLattice β] (f : β →o β) {x : β}
    (hx : x ≤ f x) : (f.nextFixed x hx : β) = nextFixedPt f x := by
  change sInf {y | (OrderHom.const β x ⊔ f) y ≤ y} = sInf {y | x ≤ y ∧ f y ≤ y}
  congr 1
  ext y
  exact sup_le_iff

end KT
