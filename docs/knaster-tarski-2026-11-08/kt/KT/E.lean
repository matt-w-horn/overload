import Mathlib.Order.FixedPoints

/-! # E: complete-lattice lemmas for `OrderHom.nextFixed` / `prevFixed` (PR_B candidates) -/

open Function (IsFixedPt)

namespace OrderHom

variable {α : Type*} [CompleteLattice α] (f : α →o α)

theorem iterate_bot_le_lfp (n : ℕ) : (⇑f)^[n] ⊥ ≤ f.lfp := by
  induction n with
  | zero => exact bot_le
  | succ n ih => rw [Function.iterate_succ_apply']; exact (f.mono ih).trans_eq f.map_lfp

theorem gfp_le_iterate_top (n : ℕ) : f.gfp ≤ (⇑f)^[n] ⊤ :=
  f.dual.iterate_bot_le_lfp n

theorem le_lfp_const_sup (x : α) : x ≤ (const α x ⊔ f).lfp :=
  (le_sup_left : x ≤ x ⊔ f (const α x ⊔ f).lfp).trans_eq (const α x ⊔ f).map_lfp

theorem gfp_const_inf_le' (x : α) : (const α x ⊓ f).gfp ≤ x :=
  f.gfp_const_inf_le x

theorem nextFixed_le_of_le {a b : α} (ha : a ≤ f a) (hb : f b ≤ b) (hab : a ≤ b) :
    (f.nextFixed a ha : α) ≤ b :=
  lfp_le _ (sup_le hab hb)

theorem le_prevFixed_of_le {a b : α} (ha : a ≤ f a) (hb : f b ≤ b) (hab : a ≤ b) :
    a ≤ (f.prevFixed b hb : α) :=
  le_gfp _ (le_inf hab ha)

theorem nextFixed_le_prevFixed {a b : α} (ha : a ≤ f a) (hb : f b ≤ b) (hab : a ≤ b) :
    (f.nextFixed a ha : α) ≤ (f.prevFixed b hb : α) :=
  lfp_le _ (sup_le (f.le_prevFixed_of_le ha hb hab) (f.prevFixed b hb).2.le)

variable {f}

theorem nextFixed_mono {g : α →o α} (hfg : f ≤ g) {x y : α} (hxy : x ≤ y) (hx : x ≤ f x)
    (hy : y ≤ g y) : (f.nextFixed x hx : α) ≤ (g.nextFixed y hy : α) :=
  lfp.mono (sup_le_sup ((const α).mono hxy) hfg)

theorem prevFixed_mono {g : α →o α} (hfg : f ≤ g) {x y : α} (hxy : x ≤ y) (hx : f x ≤ x)
    (hy : g y ≤ y) : (f.prevFixed x hx : α) ≤ (g.prevFixed y hy : α) :=
  gfp.mono (inf_le_inf ((const α).mono hxy) hfg)

theorem iterate_le_nextFixed {x : α} (hx : x ≤ f x) (n : ℕ) :
    (⇑f)^[n] x ≤ (f.nextFixed x hx : α) := by
  induction n with
  | zero => exact f.le_nextFixed hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (f.mono ih).trans_eq (f.nextFixed x hx).2.eq

theorem prevFixed_le_iterate {x : α} (hx : f x ≤ x) (n : ℕ) :
    (f.prevFixed x hx : α) ≤ (⇑f)^[n] x := by
  induction n with
  | zero => exact f.prevFixed_le hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (f.prevFixed x hx).2.eq.symm.trans_le (f.mono ih)

end OrderHom
