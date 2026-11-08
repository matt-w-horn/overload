import KT.D1
import KT.D2
import KT.D3
import KT.D4
import KT.Eq1A
import KT.Eq1B
import KT.Eq1C
import KT.Eq2
import KT.Eq3
import KT.Eq4

/-! # Agreement: under PR #42225's hypotheses, D1, D2, D3∘D2, D4∘D3 all equal `lfpIcc f a b`,
and the routes agree with each other. -/

open Function (IsFixedPt)
open Set

namespace KT

section General

variable {α : Type*} [ConditionallyCompleteLattice α] {f : α → α} {a b : α}
  (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (hf : MapsTo f (Icc a b) (Icc a b))
include hab hm hf

/-- D1 = D0 (Route 3). -/
theorem agree_D1 :
    letI : Fact (a ≤ b) := ⟨hab⟩
    ((hf.restrictOrderHom hm).lfp : α) = lfpIcc f a b :=
  coe_lfp_restrictOrderHom hab hf hm

omit hm in
/-- D3∘D2 = D0 (Route 1C, via `MapsTo`). -/
theorem agree_D3_D2 : nextFixedPt (clampIcc f a b) a = lfpIcc f a b :=
  nextFixedPt_clampIcc_eq_lfpIcc hab fun _ hz ↦ (hf hz).2

/-- D4∘D3 = D0 (Route 2). -/
theorem agree_D4_D3 :
    prefixedClosure (clampIcc f a b) (monotone_clampIcc hab hm) (bddAbove_range_clampIcc hab hf) a
      = lfpIcc f a b :=
  prefixedClosure_clampIcc_eq_lfpIcc hab hm hf

/-- D4∘D3 = D3∘D2 two ways: by `rfl` (Route 4) and by composing Routes 2 and 1C. -/
theorem agree_D4_D3_rfl :
    prefixedClosure (clampIcc f a b) (monotone_clampIcc hab hm) (bddAbove_range_clampIcc hab hf) a
      = nextFixedPt (clampIcc f a b) a := rfl

theorem agree_D4_D3_via_D0 :
    prefixedClosure (clampIcc f a b) (monotone_clampIcc hab hm) (bddAbove_range_clampIcc hab hf) a
      = nextFixedPt (clampIcc f a b) a :=
  (agree_D4_D3 hab hm hf).trans (agree_D3_D2 hab hf).symm

omit hm in
/-- D2 = D0 under the extra `Ici a` monotonicity (Route 1B). -/
theorem agree_D2_of_Ici (hm' : MonotoneOn f (Ici a)) : nextFixedPt f a = lfpIcc f a b :=
  nextFixedPt_eq_lfpIcc_of_monotoneOn_Ici hab (hf (right_mem_Icc.2 hab)).2 hm'

/-- The `Icc`-hypothesis version of `nextFixedPt ≤ prevFixedPt`, through the interval theorem. -/
theorem nextFixedPt_le_prevFixedPt_of_Icc :
    nextFixedPt f a ≤ prevFixedPt f b := by
  have h₁ : nextFixedPt f a ≤ lfpIcc f a b :=
    csInf_le_csInf ⟨a, fun _ hy ↦ hy.1⟩ ⟨b, ⟨hab, le_rfl⟩, (hf (right_mem_Icc.2 hab)).2⟩
      fun _ hx ↦ ⟨hx.1.1, hx.2⟩
  have h₂ : lfpIcc f a b ≤ gfpIcc f a b :=
    (isLeast_lfpIcc hab hm hf).2 (isGreatest_gfpIcc hab hm hf).1
  have h₃ : gfpIcc f a b ≤ prevFixedPt f b :=
    csSup_le_csSup ⟨b, fun _ hy ↦ hy.1⟩ ⟨a, ⟨le_rfl, hab⟩, (hf (left_mem_Icc.2 hab)).1⟩
      fun _ hx ↦ ⟨hx.1.2, hx.2⟩
  exact h₁.trans (h₂.trans h₃)

end General

section Linear

variable {α : Type*} [ConditionallyCompleteLinearOrder α] {f : α → α} {a b : α}
  (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (hf : MapsTo f (Icc a b) (Icc a b))
include hab hm hf

omit hm in
/-- D2 = D0 in a linear order with no monotonicity at all (Route 1A). -/
theorem agree_D2_linear : nextFixedPt f a = lfpIcc f a b :=
  nextFixedPt_eq_lfpIcc_of_linear hab (hf (right_mem_Icc.2 hab)).2

omit hm in
/-- Cross-check of Routes 1A and 1C against each other through D0. -/
theorem agree_1A_1C : nextFixedPt f a = nextFixedPt (clampIcc f a b) a :=
  (agree_D2_linear hab hf).trans (agree_D3_D2 hab hf).symm

end Linear

end KT
