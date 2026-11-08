import KT.Defs

/-! # D2: anchored extremal fixed points, `nextFixedPt` / `prevFixedPt` -/

open Function (IsFixedPt)
open Set

namespace KT

section General

variable {α : Type*} [ConditionallyCompleteLattice α] {f g : α → α} {a b x : α}

theorem le_nextFixedPt (hb : ∃ b, a ≤ b ∧ f b ≤ b) : a ≤ nextFixedPt f a :=
  le_csInf hb fun _ hx ↦ hx.1

theorem nextFixedPt_le (hax : a ≤ x) (hfx : f x ≤ x) : nextFixedPt f a ≤ x :=
  csInf_le ⟨a, fun _ hy ↦ hy.1⟩ ⟨hax, hfx⟩

theorem prevFixedPt_le (ha : ∃ a, a ≤ b ∧ a ≤ f a) : prevFixedPt f b ≤ b :=
  csSup_le ha fun _ hx ↦ hx.1

theorem le_prevFixedPt (hxb : x ≤ b) (hxf : x ≤ f x) : x ≤ prevFixedPt f b :=
  le_csSup ⟨b, fun _ hy ↦ hy.1⟩ ⟨hxb, hxf⟩

/-- Monotone in the map and in the anchor; no monotonicity of `f`, `g` is needed. -/
theorem nextFixedPt_mono {a₁ a₂ : α} (ha : a₁ ≤ a₂) (hfg : ∀ x, a₂ ≤ x → f x ≤ g x)
    (hb : ∃ b, a₂ ≤ b ∧ g b ≤ b) : nextFixedPt f a₁ ≤ nextFixedPt g a₂ :=
  csInf_le_csInf ⟨a₁, fun _ hy ↦ hy.1⟩ hb fun _ hx ↦ ⟨ha.trans hx.1, (hfg _ hx.1).trans hx.2⟩

theorem prevFixedPt_mono {b₁ b₂ : α} (hb : b₁ ≤ b₂) (hfg : ∀ x, x ≤ b₁ → f x ≤ g x)
    (ha : ∃ a, a ≤ b₁ ∧ a ≤ f a) : prevFixedPt f b₁ ≤ prevFixedPt g b₂ :=
  csSup_le_csSup ⟨b₂, fun _ hy ↦ hy.1⟩ ha fun _ hx ↦ ⟨hx.1.trans hb, hx.2.trans (hfg _ hx.1)⟩

/-- Knaster–Tarski above `a` in a conditionally complete lattice. -/
theorem isLeast_nextFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a)
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) : IsLeast {x | a ≤ x ∧ IsFixedPt f x} (nextFixedPt f a) := by
  have hap : a ≤ nextFixedPt f a := le_nextFixedPt hb
  have h₁ : f (nextFixedPt f a) ≤ nextFixedPt f a :=
    le_csInf hb fun x hx ↦ (hm hap hx.1 (nextFixedPt_le hx.1 hx.2)).trans hx.2
  have haf : a ≤ f (nextFixedPt f a) := ha.trans (hm (mem_Ici.2 le_rfl) hap hap)
  have h₂ : nextFixedPt f a ≤ f (nextFixedPt f a) := nextFixedPt_le haf (hm haf hap h₁)
  exact ⟨⟨hap, h₁.antisymm h₂⟩, fun _ hx ↦ nextFixedPt_le hx.1 hx.2.le⟩

theorem isGreatest_prevFixedPt (hm : MonotoneOn f (Iic b)) (hb : f b ≤ b)
    (ha : ∃ a, a ≤ b ∧ a ≤ f a) :
    IsGreatest {x | x ≤ b ∧ IsFixedPt f x} (prevFixedPt f b) :=
  isLeast_nextFixedPt (α := αᵒᵈ) hm.dual hb ha

theorem isFixedPt_nextFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a)
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) : IsFixedPt f (nextFixedPt f a) :=
  (isLeast_nextFixedPt hm ha hb).1.2

theorem iterate_le_nextFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a)
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) (n : ℕ) : f^[n] a ≤ nextFixedPt f a := by
  obtain ⟨⟨hap, hfix⟩, -⟩ := isLeast_nextFixedPt hm ha hb
  suffices h : a ≤ f^[n] a ∧ f^[n] a ≤ nextFixedPt f a from h.2
  induction n with
  | zero => exact ⟨le_rfl, hap⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ha.trans (hm (mem_Ici.2 le_rfl) ih.1 ih.1), (hm ih.1 hap ih.2).trans_eq hfix.eq⟩

/-- Stated with monotonicity on `Ici a` (one-sided Knaster–Tarski suffices). The variant with
`MonotoneOn f (Icc a b)` is true but needs the two-sided interval theorem; see `Agreement`. -/
theorem nextFixedPt_le_prevFixedPt (hm : MonotoneOn f (Ici a)) (ha : a ≤ f a) (hab : a ≤ b)
    (hb : f b ≤ b) : nextFixedPt f a ≤ prevFixedPt f b :=
  le_prevFixedPt (nextFixedPt_le hab hb) (isFixedPt_nextFixedPt hm ha ⟨b, hab, hb⟩).ge

/-- D7: comparative statics in a parameter. -/
theorem nextFixedPt_mono_param {Λ : Type*} [Preorder Λ] {F : Λ → α → α}
    (hF : ∀ x, a ≤ x → Monotone (F · x)) (hb : ∀ l, ∃ b, a ≤ b ∧ F l b ≤ b) :
    Monotone fun l ↦ nextFixedPt (F l) a :=
  fun _ _ hl ↦ nextFixedPt_mono le_rfl (fun x hx ↦ hF x hx hl) (hb _)

theorem prevFixedPt_mono_param {Λ : Type*} [Preorder Λ] {F : Λ → α → α}
    (hF : ∀ x, x ≤ b → Monotone (F · x)) (ha : ∀ l, ∃ a, a ≤ b ∧ a ≤ F l a) :
    Monotone fun l ↦ prevFixedPt (F l) b :=
  fun _ _ hl ↦ prevFixedPt_mono le_rfl (fun x hx ↦ hF x hx hl) (ha _)

end General

section Linear

variable {α : Type*} [ConditionallyCompleteLinearOrder α] {f : α → α} {a b : α}

/-- In a linear order, monotonicity on `Icc a b` suffices. -/
theorem isLeast_nextFixedPt_of_linear (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a)
    (hb : f b ≤ b) : IsLeast {x ∈ Icc a b | IsFixedPt f x} (nextFixedPt f a) := by
  have hpb : nextFixedPt f a ≤ b := nextFixedPt_le hab hb
  have hap : a ≤ nextFixedPt f a := le_nextFixedPt ⟨b, hab, hb⟩
  have hp : nextFixedPt f a ∈ Icc a b := ⟨hap, hpb⟩
  have h₁ : f (nextFixedPt f a) ≤ nextFixedPt f a := by
    refine le_csInf ⟨b, hab, hb⟩ fun x hx ↦ ?_
    rcases le_total x b with hxb | hbx
    · exact (hm hp ⟨hx.1, hxb⟩ (nextFixedPt_le hx.1 hx.2)).trans hx.2
    · exact (hm hp (right_mem_Icc.2 hab) hpb).trans (hb.trans hbx)
  have haf : a ≤ f (nextFixedPt f a) := ha.trans (hm (left_mem_Icc.2 hab) hp hap)
  have h₂ : nextFixedPt f a ≤ f (nextFixedPt f a) :=
    nextFixedPt_le haf (hm ⟨haf, h₁.trans hpb⟩ hp h₁)
  exact ⟨⟨hp, h₁.antisymm h₂⟩, fun _ hx ↦ nextFixedPt_le hx.1.1 hx.2.le⟩

end Linear

section Bridge

variable {β : Type*} [CompleteLattice β]

/-- Bridge to Mathlib: `OrderHom.nextFixed` is `nextFixedPt` on a complete lattice. -/
theorem _root_.OrderHom.coe_nextFixed_eq_nextFixedPt (f : β →o β) {x : β} (hx : x ≤ f x) :
    (f.nextFixed x hx : β) = nextFixedPt f x := by
  change sInf {y | (OrderHom.const β x ⊔ f) y ≤ y} = sInf {y | x ≤ y ∧ f y ≤ y}
  congr 1
  ext y
  exact sup_le_iff

theorem _root_.OrderHom.coe_prevFixed_eq_prevFixedPt (f : β →o β) {x : β} (hx : f x ≤ x) :
    (f.prevFixed x hx : β) = prevFixedPt f x := by
  change sSup {y | y ≤ (OrderHom.const β x ⊓ f) y} = sSup {y | y ≤ x ∧ y ≤ f y}
  congr 1
  ext y
  exact le_inf_iff

end Bridge

end KT
