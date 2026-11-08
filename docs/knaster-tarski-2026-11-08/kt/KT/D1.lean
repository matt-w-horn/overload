import KT.Defs
import Mathlib.Order.CompleteLatticeIntervals

/-! # D1: the subtype bridge `↑(lfp (restriction of f to Icc a b)) = lfpIcc f a b` -/

open Function (IsFixedPt fixedPoints)
open Set

namespace KT

section RestrictOrderHom

variable {α β : Type*} [Preorder α] [Preorder β] {f : α → β} {s : Set α} {t : Set β}

/-- Bundle `MapsTo f s t` and `MonotoneOn f s` into an order hom `s →o t`. -/
def _root_.Set.MapsTo.restrictOrderHom (hm : MapsTo f s t) (hf : MonotoneOn f s) : s →o t where
  toFun := hm.restrict f s t
  monotone' x y hxy := hf x.2 y.2 hxy

@[simp] theorem coe_restrictOrderHom_apply (hm : MapsTo f s t) (hf : MonotoneOn f s) (x : s) :
    (hm.restrictOrderHom hf x : β) = f x := rfl

end RestrictOrderHom

section Bridge

variable {α : Type*} [ConditionallyCompleteLattice α] {f : α → α} {a b : α}

/-- Route 3: the coercion of Mathlib's `lfp` of the restriction is the PR's `lfpIcc`. -/
theorem coe_lfp_restrictOrderHom (hab : a ≤ b) (hm : MapsTo f (Icc a b) (Icc a b))
    (hf : MonotoneOn f (Icc a b)) :
    letI : Fact (a ≤ b) := ⟨hab⟩
    ((hm.restrictOrderHom hf).lfp : α) = lfpIcc f a b := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  have hne : {x : Icc a b | hm.restrictOrderHom hf x ≤ x}.Nonempty :=
    ⟨⟨b, right_mem_Icc.2 hab⟩, (hm (right_mem_Icc.2 hab)).2⟩
  change ((sInf {x : Icc a b | hm.restrictOrderHom hf x ≤ x} : Icc a b) : α) = _
  rw [Set.Icc.coe_sInf hab hne]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
    exact ⟨hy, hfy⟩
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩

theorem coe_gfp_restrictOrderHom (hab : a ≤ b) (hm : MapsTo f (Icc a b) (Icc a b))
    (hf : MonotoneOn f (Icc a b)) :
    letI : Fact (a ≤ b) := ⟨hab⟩
    ((hm.restrictOrderHom hf).gfp : α) = gfpIcc f a b := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  have hne : {x : Icc a b | x ≤ hm.restrictOrderHom hf x}.Nonempty :=
    ⟨⟨a, left_mem_Icc.2 hab⟩, (hm (left_mem_Icc.2 hab)).1⟩
  change ((sSup {x : Icc a b | x ≤ hm.restrictOrderHom hf x} : Icc a b) : α) = _
  rw [Set.Icc.coe_sSup hab hne]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
    exact ⟨hy, hfy⟩
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩

/-- Knaster–Tarski on `Icc a b`, transported from `OrderHom.isLeast_lfp` through the bridge. -/
theorem isLeast_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsLeast {x ∈ Icc a b | IsFixedPt f x} (lfpIcc f a b) := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  set g := hf.restrictOrderHom hm
  have h := g.isLeast_lfp
  rw [← coe_lfp_restrictOrderHom hab hf hm]
  refine ⟨⟨g.lfp.2, congrArg Subtype.val h.1⟩, fun x hx ↦ ?_⟩
  exact Subtype.coe_le_coe.2 (h.2 (show ⟨x, hx.1⟩ ∈ fixedPoints g from Subtype.ext hx.2))

theorem isGreatest_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsGreatest {x ∈ Icc a b | IsFixedPt f x} (gfpIcc f a b) := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  set g := hf.restrictOrderHom hm
  have h := g.isGreatest_gfp
  rw [← coe_gfp_restrictOrderHom hab hf hm]
  refine ⟨⟨g.gfp.2, congrArg Subtype.val h.1⟩, fun x hx ↦ ?_⟩
  exact Subtype.coe_le_coe.2 (h.2 (show ⟨x, hx.1⟩ ∈ fixedPoints g from Subtype.ext hx.2))

end Bridge

end KT
