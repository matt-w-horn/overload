import KT.D1

/-! # Route 3 (bridge): restated from D1 — `↑(lfp (restriction)) = lfpIcc f a b` via
`Set.Icc.coe_sInf` and set-image equality. The proof lives in `KT.D1.coe_lfp_restrictOrderHom`.
Does not import D2/D3/D4 or any Eq file. -/

open Set

namespace KT

variable {α : Type*} [ConditionallyCompleteLattice α] {f : α → α} {a b : α}

theorem route3 (hab : a ≤ b) (hm : MapsTo f (Icc a b) (Icc a b)) (hf : MonotoneOn f (Icc a b)) :
    letI : Fact (a ≤ b) := ⟨hab⟩
    ((hm.restrictOrderHom hf).lfp : α) = lfpIcc f a b :=
  coe_lfp_restrictOrderHom hab hm hf

end KT
