import KT.Defs

/-! # Route 1A (linear order): `nextFixedPt f a = lfpIcc f a b` from `a ≤ b` and `f b ≤ b` only.
No monotonicity, no `a ≤ f a`. Independent of every other route. -/

open Set

namespace KT

variable {α : Type*} [ConditionallyCompleteLinearOrder α] {f : α → α} {a b : α}

theorem nextFixedPt_eq_lfpIcc_of_linear (hab : a ≤ b) (hb : f b ≤ b) :
    nextFixedPt f a = lfpIcc f a b := by
  refine csInf_eq_csInf_of_forall_exists_le (fun x hx ↦ ?_) (fun y hy ↦ ⟨y, ⟨hy.1.1, hy.2⟩, le_rfl⟩)
  rcases le_total x b with hxb | hbx
  · exact ⟨x, ⟨⟨hx.1, hxb⟩, hx.2⟩, le_rfl⟩
  · exact ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩, hbx⟩

theorem prevFixedPt_eq_gfpIcc_of_linear (hab : a ≤ b) (ha : a ≤ f a) :
    prevFixedPt f b = gfpIcc f a b := by
  refine csSup_eq_csSup_of_forall_exists_le (fun x hx ↦ ?_) (fun y hy ↦ ⟨y, ⟨hy.1.2, hy.2⟩, le_rfl⟩)
  rcases le_total a x with hax | hxa
  · exact ⟨x, ⟨⟨hax, hx.1⟩, hx.2⟩, le_rfl⟩
  · exact ⟨a, ⟨⟨le_rfl, hab⟩, ha⟩, hxa⟩

end KT
