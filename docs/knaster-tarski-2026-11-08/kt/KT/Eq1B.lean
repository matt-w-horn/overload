import KT.Defs

/-! # Route 1B (general ccl): `nextFixedPt f a = lfpIcc f a b` from `a ≤ b`, `f b ≤ b`,
`MonotoneOn f (Ici a)`. Witness `x ⊓ b`. Independent of every other route. -/

open Set

namespace KT

variable {α : Type*} [ConditionallyCompleteLattice α] {f : α → α} {a b : α}

theorem nextFixedPt_eq_lfpIcc_of_monotoneOn_Ici (hab : a ≤ b) (hb : f b ≤ b)
    (hm : MonotoneOn f (Ici a)) : nextFixedPt f a = lfpIcc f a b := by
  apply le_antisymm
  · exact csInf_le_csInf ⟨a, fun _ hy ↦ hy.1⟩ ⟨b, ⟨hab, le_rfl⟩, hb⟩ fun _ hx ↦ ⟨hx.1.1, hx.2⟩
  · refine le_csInf ⟨b, hab, hb⟩ fun x hx ↦ ?_
    have hxb : a ≤ x ⊓ b := le_inf hx.1 hab
    have hfx : f (x ⊓ b) ≤ x ⊓ b :=
      le_inf ((hm hxb hx.1 inf_le_left).trans hx.2) ((hm hxb hab inf_le_right).trans hb)
    have h : lfpIcc f a b ≤ x ⊓ b := csInf_le ⟨a, fun _ hy ↦ hy.1.1⟩ ⟨⟨hxb, inf_le_right⟩, hfx⟩
    exact h.trans inf_le_left

end KT
