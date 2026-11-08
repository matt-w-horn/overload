import KT.D1
import KT.D3
import KT.D4

/-! # Route 2 (uniqueness): two `IsLeast` witnesses for `{x ∈ Icc a b | IsFixedPt f x}` are equal.
Connects D1 (Mathlib's `isLeast_lfp` transported) with D4 ∘ D3 (`prefixedClosure` of the clamp)
under exactly PR #42225's hypotheses. Does not import Eq1A/Eq1B/Eq1C. -/

open Function (IsFixedPt)
open Set

namespace KT

variable {α : Type*} [ConditionallyCompleteLattice α] {f : α → α} {a b : α}

/-- The closed-under-`a` fixed points of the clamp are the fixed points of `f` in `Icc a b`. -/
theorem setOf_fixedPt_clampIcc (hab : a ≤ b) (hf : MapsTo f (Icc a b) (Icc a b)) :
    {x | a ≤ x ∧ IsFixedPt (clampIcc f a b) x} = {x ∈ Icc a b | IsFixedPt f x} := by
  ext x
  constructor
  · rintro ⟨_, hx⟩
    exact (isFixedPt_clampIcc_iff hab hf).1 hx
  · rintro ⟨hmem, hx⟩
    exact ⟨hmem.1, (isFixedPt_clampIcc_iff hab hf).2 ⟨hmem, hx⟩⟩

theorem isLeast_prefixedClosure_clampIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    IsLeast {x ∈ Icc a b | IsFixedPt f x}
      (prefixedClosure (clampIcc f a b) (monotone_clampIcc hab hm)
        (bddAbove_range_clampIcc hab hf) a) := by
  rw [← setOf_fixedPt_clampIcc hab hf]
  exact isLeast_prefixedClosure _ _ (clampIcc_mem_Icc hab hf a).1

/-- Route 2: D4∘D3 equals D1's transported `lfp`, by uniqueness of the least element. -/
theorem prefixedClosure_clampIcc_eq_lfpIcc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hf : MapsTo f (Icc a b) (Icc a b)) :
    prefixedClosure (clampIcc f a b) (monotone_clampIcc hab hm) (bddAbove_range_clampIcc hab hf) a
      = lfpIcc f a b :=
  (isLeast_prefixedClosure_clampIcc hab hm hf).unique (isLeast_lfpIcc hab hm hf)

end KT
