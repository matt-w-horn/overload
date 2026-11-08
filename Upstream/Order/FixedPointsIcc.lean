/-
Copyright (c) 2026 Matthew W. Horn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew W. Horn
-/
module

public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.FixedPoints

/-!
# Knaster-Tarski fixed points on an interval

If `f : α → α` is monotone on `Icc a b` in a conditionally complete lattice and maps `Icc a b`
into itself, then `f` has a least and a greatest fixed point in `Icc a b`.

## Main definitions

* `lfpIcc f a b`, `gfpIcc f a b`: the least and greatest fixed points of `f` in `Icc a b`,
  defined as the infimum of the prefixed points and the supremum of the postfixed points.
* `Set.MapsTo.restrictOrderHom`: `MapsTo f s t` and `MonotoneOn f s` bundled as `s →o t`.

## Main results

* `coe_lfp_restrictOrderHom`, `coe_gfp_restrictOrderHom`: `lfpIcc f a b` is the coercion of
  mathlib's `OrderHom.lfp` of the restriction of `f` to `Icc a b` with `Set.Icc.completeLattice`.
* `isLeast_lfpIcc`, `isGreatest_gfpIcc`: the Knaster-Tarski theorem on `Icc a b`, transported
  from `OrderHom.isLeast_lfp` through the bridge. `isFixedPt_lfpIcc`, `isFixedPt_gfpIcc`,
  `lfpIcc_le_gfpIcc` are its projections.
* `iterate_le_lfpIcc`, `gfpIcc_le_iterate`: the orbits of the endpoints bracket the extreme
  fixed points.
* `lfpIcc_le_lfpIcc`, `gfpIcc_le_gfpIcc`: `lfpIcc` and `gfpIcc` are monotone in `f`.

## Implementation notes

The definitions return elements of `α` and take `MonotoneOn` and `MapsTo` hypotheses, which is
the convenient form on intervals of `ℝ`. Every fixed-point fact routes through mathlib's
`OrderHom.lfp` on the subtype `↥(Icc a b)`; nothing is re-proved from `csInf`. Without the
hypotheses the definitions are junk values.

## Tags

fixed point, Knaster-Tarski, conditionally complete lattice, interval
-/

public section

open Function (IsFixedPt fixedPoints)
open Set

section RestrictOrderHom

variable {α β : Type*} [Preorder α] [Preorder β] {f : α → β} {s : Set α} {t : Set β}

/-- `MapsTo f s t` and `MonotoneOn f s` bundled as an order hom `s →o t`. -/
@[expose] def Set.MapsTo.restrictOrderHom (hm : MapsTo f s t) (hf : MonotoneOn f s) : s →o t where
  toFun := hm.restrict f s t
  monotone' x y hxy := hf x.2 y.2 hxy

@[simp] theorem Set.MapsTo.coe_restrictOrderHom_apply (hm : MapsTo f s t) (hf : MonotoneOn f s)
    (x : s) : (hm.restrictOrderHom hf x : β) = f x := rfl

end RestrictOrderHom

variable {α : Type*} [ConditionallyCompleteLattice α] {f g : α → α} {a b c x : α}

/-- The least fixed point of `f` in `Icc a b`: the infimum of the prefixed points of `f` in
`Icc a b`. This is the least fixed point when `f` is monotone on `Icc a b` and maps `Icc a b` into
itself (`isLeast_lfpIcc`). -/
@[expose] def lfpIcc (f : α → α) (a b : α) : α :=
  sInf {x ∈ Icc a b | f x ≤ x}

/-- The greatest fixed point of `f` in `Icc a b`: the supremum of the postfixed points of `f` in
`Icc a b`. This is the greatest fixed point when `f` is monotone on `Icc a b` and maps `Icc a b`
into itself (`isGreatest_gfpIcc`). -/
@[expose, to_dual existing (reorder := a b)] def gfpIcc (f : α → α) (a b : α) : α :=
  sSup {x ∈ Icc a b | x ≤ f x}

@[to_dual (reorder := a b) (rename := a ↔ b) le_gfpIcc]
theorem lfpIcc_le (hx : x ∈ Icc a b) (hfx : f x ≤ x) : lfpIcc f a b ≤ x :=
  csInf_le ⟨a, fun _ hy ↦ hy.1.1⟩ ⟨hx, hfx⟩

@[to_dual (reorder := a b) (rename := a ↔ b) gfpIcc_le]
theorem le_lfpIcc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, f x ≤ x → c ≤ x) : c ≤ lfpIcc f a b :=
  le_csInf ⟨b, right_mem_Icc.mpr hab, (hf (right_mem_Icc.mpr hab)).2⟩ fun _ hx ↦ h _ hx.1 hx.2

/-- `lfpIcc f a b` lies in `Icc a b`. -/
@[to_dual (reorder := a b) (rename := a ↔ b) /-- `gfpIcc f a b` lies in `Icc a b`. -/]
theorem lfpIcc_mem_Icc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    lfpIcc f a b ∈ Icc a b :=
  ⟨le_lfpIcc hab hf fun _ hx _ ↦ hx.1,
    lfpIcc_le (right_mem_Icc.mpr hab) (hf (right_mem_Icc.mpr hab)).2⟩

/-- The bridge to mathlib: `lfpIcc f a b` is the coercion of `OrderHom.lfp` of the restriction of
`f` to `Icc a b`, with the complete lattice structure `Set.Icc.completeLattice`. -/
theorem coe_lfp_restrictOrderHom (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b))
    (hm : MonotoneOn f (Icc a b)) :
    letI : Fact (a ≤ b) := ⟨hab⟩
    ((hf.restrictOrderHom hm).lfp : α) = lfpIcc f a b := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  have hne : {x : Icc a b | hf.restrictOrderHom hm x ≤ x}.Nonempty :=
    ⟨⟨b, right_mem_Icc.2 hab⟩, (hf (right_mem_Icc.2 hab)).2⟩
  change ((sInf {x : Icc a b | hf.restrictOrderHom hm x ≤ x} : Icc a b) : α) = _
  rw [Set.Icc.coe_sInf hab hne]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
    exact ⟨hy, hfy⟩
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩

/-- The bridge to mathlib: `gfpIcc f a b` is the coercion of `OrderHom.gfp` of the restriction of
`f` to `Icc a b`, with the complete lattice structure `Set.Icc.completeLattice`. -/
theorem coe_gfp_restrictOrderHom (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b))
    (hm : MonotoneOn f (Icc a b)) :
    letI : Fact (a ≤ b) := ⟨hab⟩
    ((hf.restrictOrderHom hm).gfp : α) = gfpIcc f a b := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  have hne : {x : Icc a b | x ≤ hf.restrictOrderHom hm x}.Nonempty :=
    ⟨⟨a, left_mem_Icc.2 hab⟩, (hf (left_mem_Icc.2 hab)).1⟩
  change ((sSup {x : Icc a b | x ≤ hf.restrictOrderHom hm x} : Icc a b) : α) = _
  rw [Set.Icc.coe_sSup hab hne]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hfy, rfl⟩
    exact ⟨hy, hfy⟩
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩

/-- **Knaster-Tarski on `Icc a b`**: `lfpIcc f a b` is the least fixed point of `f` in `Icc a b`.
Transported from `OrderHom.isLeast_lfp` through `coe_lfp_restrictOrderHom`. -/
theorem isLeast_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsLeast {x ∈ Icc a b | IsFixedPt f x} (lfpIcc f a b) := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  set g := hf.restrictOrderHom hm
  have h := g.isLeast_lfp
  rw [← coe_lfp_restrictOrderHom hab hf hm]
  refine ⟨⟨g.lfp.2, congrArg Subtype.val h.1⟩, fun x hx ↦ ?_⟩
  exact Subtype.coe_le_coe.2 (h.2 (show ⟨x, hx.1⟩ ∈ fixedPoints g from Subtype.ext hx.2))

/-- **Knaster-Tarski on `Icc a b`**: `gfpIcc f a b` is the greatest fixed point of `f` in
`Icc a b`. Transported from `OrderHom.isGreatest_gfp` through `coe_gfp_restrictOrderHom`. -/
@[to_dual existing]
theorem isGreatest_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsGreatest {x ∈ Icc a b | IsFixedPt f x} (gfpIcc f a b) := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  set g := hf.restrictOrderHom hm
  have h := g.isGreatest_gfp
  rw [← coe_gfp_restrictOrderHom hab hf hm]
  refine ⟨⟨g.gfp.2, congrArg Subtype.val h.1⟩, fun x hx ↦ ?_⟩
  exact Subtype.coe_le_coe.2 (h.2 (show ⟨x, hx.1⟩ ∈ fixedPoints g from Subtype.ext hx.2))

/-- `lfpIcc f a b` is a fixed point of `f` when `f` is monotone on `Icc a b` and maps `Icc a b`
into itself. -/
theorem isFixedPt_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : IsFixedPt f (lfpIcc f a b) :=
  (isLeast_lfpIcc hab hm hf).1.2

/-- `gfpIcc f a b` is a fixed point of `f` when `f` is monotone on `Icc a b` and maps `Icc a b`
into itself. -/
@[to_dual existing]
theorem isFixedPt_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : IsFixedPt f (gfpIcc f a b) :=
  (isGreatest_gfpIcc hab hm hf).1.2

/-- The least fixed point in `Icc a b` is at most the greatest one. -/
@[to_dual self]
theorem lfpIcc_le_gfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) : lfpIcc f a b ≤ gfpIcc f a b :=
  (isLeast_lfpIcc hab hm hf).2 (isGreatest_gfpIcc hab hm hf).1

/-- The orbit of the left endpoint stays below the least fixed point. -/
@[to_dual (reorder := a b) (rename := a ↔ b) gfpIcc_le_iterate
  /-- The orbit of the right endpoint stays above the greatest fixed point. -/]
theorem iterate_le_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) (n : ℕ) : f^[n] a ≤ lfpIcc f a b := by
  induction n with
  | zero => exact (lfpIcc_mem_Icc hab hf).1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hm (hf.iterate n (left_mem_Icc.mpr hab)) (lfpIcc_mem_Icc hab hf) ih).trans_eq
      (isFixedPt_lfpIcc hab hm hf).eq

/-- `lfpIcc` is monotone in the function: if `f ≤ g` pointwise on `Icc a b`, then
`lfpIcc f a b ≤ lfpIcc g a b`. This compares the defining infima, so it needs no monotonicity. -/
@[to_dual (reorder := a b, f g) (rename := a ↔ b, f ↔ g, hg → hf)
  /-- `gfpIcc` is monotone in the function: if `f ≤ g` pointwise on `Icc a b`, then
  `gfpIcc f a b ≤ gfpIcc g a b`. This compares the defining suprema, so it needs no
  monotonicity. -/]
theorem lfpIcc_le_lfpIcc (hab : a ≤ b) (hg : MapsTo g (Icc a b) (Icc a b))
    (h : ∀ x ∈ Icc a b, f x ≤ g x) : lfpIcc f a b ≤ lfpIcc g a b :=
  csInf_le_csInf ⟨a, fun _ hy ↦ hy.1.1⟩
    ⟨b, right_mem_Icc.mpr hab, (hg (right_mem_Icc.mpr hab)).2⟩
    fun x hx ↦ ⟨hx.1, (h x hx.1).trans hx.2⟩
