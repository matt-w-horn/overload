import KT.Defs

/-! # Route 1C (clamped, general ccl): `nextFixedPt (clampIcc f a b) a = lfpIcc f a b` from
`a ≤ b` and `∀ z ∈ Icc a b, f z ≤ b` only. No monotonicity, no `a ≤ f a`.
Independent of every other route (does not import D3's lemmas). -/

open Set

namespace KT

variable {α : Type*} [ConditionallyCompleteLattice α] {f : α → α} {a b : α}

theorem nextFixedPt_clampIcc_eq_lfpIcc (hab : a ≤ b) (hfb : ∀ z ∈ Icc a b, f z ≤ b) :
    nextFixedPt (clampIcc f a b) a = lfpIcc f a b := by
  have hb : f b ≤ b := hfb b ⟨hab, le_rfl⟩
  have hclamp : ∀ x, a ≤ x → clampIcc f a b x = f (x ⊓ b) := fun x hx ↦ by
    rw [clampIcc, sup_eq_left.2 hx]
  apply le_antisymm
  · refine csInf_le_csInf ⟨a, fun _ hy ↦ hy.1⟩ ⟨b, ⟨hab, le_rfl⟩, hb⟩ fun x hx ↦ ⟨hx.1.1, ?_⟩
    rw [hclamp x hx.1.1, inf_eq_left.2 hx.1.2]
    exact hx.2
  · refine le_csInf ⟨b, hab, by rw [hclamp b hab, inf_idem]; exact hb⟩ fun x hx ↦ ?_
    have hxb : x ⊓ b ∈ Icc a b := ⟨le_inf hx.1 hab, inf_le_right⟩
    have hfx : f (x ⊓ b) ≤ x ⊓ b := by
      have := hx.2
      rw [hclamp x hx.1] at this
      exact le_inf this (hfb _ hxb)
    have h : lfpIcc f a b ≤ x ⊓ b := csInf_le ⟨a, fun _ hy ↦ hy.1.1⟩ ⟨hxb, hfx⟩
    exact h.trans inf_le_left

end KT
