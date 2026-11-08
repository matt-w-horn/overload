import KT.Defs

/-! # D3: the lattice clamp `clampIcc f a b x = f ((x ⊔ a) ⊓ b)` -/

open Function (IsFixedPt)
open Set

namespace KT

variable {α : Type*} [Lattice α] {f : α → α} {a b x : α}

theorem clamp_mem_Icc (hab : a ≤ b) (x : α) : (x ⊔ a) ⊓ b ∈ Icc a b :=
  ⟨le_inf le_sup_right hab, inf_le_right⟩

theorem clamp_eq_of_mem (hx : x ∈ Icc a b) : (x ⊔ a) ⊓ b = x := by
  rw [sup_eq_left.2 hx.1, inf_eq_left.2 hx.2]

theorem clampIcc_eq_of_mem (f : α → α) (hx : x ∈ Icc a b) : clampIcc f a b x = f x := by
  rw [clampIcc, clamp_eq_of_mem hx]

/-- The clamp turns `MonotoneOn f (Icc a b)` into global monotonicity, in any lattice. -/
theorem monotone_clampIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) :
    Monotone (clampIcc f a b) := fun _ _ hxy ↦
  hm (clamp_mem_Icc hab _) (clamp_mem_Icc hab _) (inf_le_inf_right _ (sup_le_sup_right hxy _))

theorem clampIcc_mem_Icc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) (x : α) :
    clampIcc f a b x ∈ Icc a b :=
  hf (clamp_mem_Icc hab x)

theorem bddAbove_range_clampIcc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    BddAbove (range (clampIcc f a b)) :=
  ⟨b, by rintro _ ⟨x, rfl⟩; exact (clampIcc_mem_Icc hab hf x).2⟩

theorem bddBelow_range_clampIcc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    BddBelow (range (clampIcc f a b)) :=
  ⟨a, by rintro _ ⟨x, rfl⟩; exact (clampIcc_mem_Icc hab hf x).1⟩

theorem isFixedPt_clampIcc_iff (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsFixedPt (clampIcc f a b) x ↔ x ∈ Icc a b ∧ IsFixedPt f x := by
  constructor
  · intro hx
    have hmem : x ∈ Icc a b := hx.eq ▸ clampIcc_mem_Icc hab hf x
    exact ⟨hmem, (clampIcc_eq_of_mem f hmem).symm.trans hx.eq⟩
  · rintro ⟨hmem, hx⟩
    exact (clampIcc_eq_of_mem f hmem).trans hx.eq

end KT
