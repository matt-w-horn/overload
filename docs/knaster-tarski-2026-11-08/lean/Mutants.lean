import KT
/-! Each `theorem` below is a deliberately wrong variant of a main theorem (one hypothesis dropped
or one inequality reversed), proved with the original proof. Every one of them must FAIL. -/
open Function (IsFixedPt) Set KT

section
variable {α : Type*} [ConditionallyCompleteLattice α] {f g : α → α} {a b x : α}

-- M1: isLeast_nextFixedPt without `a ≤ f a`
theorem M1 (hm : MonotoneOn f (Ici a))
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) : IsLeast {x | a ≤ x ∧ IsFixedPt f x} (nextFixedPt f a) := by
  have hap : a ≤ nextFixedPt f a := le_nextFixedPt hb
  have h₁ : f (nextFixedPt f a) ≤ nextFixedPt f a :=
    le_csInf hb fun x hx ↦ (hm hap hx.1 (nextFixedPt_le hx.1 hx.2)).trans hx.2
  have haf : a ≤ f (nextFixedPt f a) := (hm (mem_Ici.2 le_rfl) hap hap)
  have h₂ : nextFixedPt f a ≤ f (nextFixedPt f a) := nextFixedPt_le haf (hm haf hap h₁)
  exact ⟨⟨hap, h₁.antisymm h₂⟩, fun _ hx ↦ nextFixedPt_le hx.1 hx.2.le⟩

-- M2: isLeast_nextFixedPt without monotonicity
theorem M2 (ha : a ≤ f a)
    (hb : ∃ b, a ≤ b ∧ f b ≤ b) : IsLeast {x | a ≤ x ∧ IsFixedPt f x} (nextFixedPt f a) := by
  have hap : a ≤ nextFixedPt f a := le_nextFixedPt hb
  have h₁ : f (nextFixedPt f a) ≤ nextFixedPt f a :=
    le_csInf hb fun x hx ↦ (nextFixedPt_le hx.1 hx.2).trans hx.2
  exact ⟨⟨hap, h₁.antisymm (nextFixedPt_le ha h₁)⟩, fun _ hx ↦ nextFixedPt_le hx.1 hx.2.le⟩

-- M3: nextFixedPt_le with the anchor inequality reversed
theorem M3 (hax : x ≤ a) (hfx : f x ≤ x) : nextFixedPt f a ≤ x :=
  csInf_le ⟨a, fun _ hy ↦ hy.1⟩ ⟨hax, hfx⟩

-- M4: nextFixedPt_mono with anchors reversed
theorem M4 {a₁ a₂ : α} (ha : a₂ ≤ a₁) (hfg : ∀ x, a₂ ≤ x → f x ≤ g x)
    (hb : ∃ b, a₂ ≤ b ∧ g b ≤ b) : nextFixedPt f a₁ ≤ nextFixedPt g a₂ :=
  csInf_le_csInf ⟨a₁, fun _ hy ↦ hy.1⟩ hb fun _ hx ↦ ⟨ha.trans hx.1, (hfg _ hx.1).trans hx.2⟩

-- M5: nextFixedPt_mono with the pointwise inequality reversed
theorem M5 {a₁ a₂ : α} (ha : a₁ ≤ a₂) (hfg : ∀ x, a₂ ≤ x → g x ≤ f x)
    (hb : ∃ b, a₂ ≤ b ∧ g b ≤ b) : nextFixedPt f a₁ ≤ nextFixedPt g a₂ :=
  csInf_le_csInf ⟨a₁, fun _ hy ↦ hy.1⟩ hb fun _ hx ↦ ⟨ha.trans hx.1, (hfg _ hx.1).trans hx.2⟩

-- M8: Route 1C without `∀ z ∈ Icc a b, f z ≤ b`
theorem M8 (hab : a ≤ b) : nextFixedPt (clampIcc f a b) a = lfpIcc f a b := by
  have hclamp : ∀ x, a ≤ x → clampIcc f a b x = f (x ⊓ b) := fun x hx ↦ by
    rw [clampIcc, sup_eq_left.2 hx]
  apply le_antisymm
  · refine csInf_le_csInf ⟨a, fun _ hy ↦ hy.1⟩ ⟨b, ⟨hab, le_rfl⟩, ?_⟩ fun x hx ↦ ⟨hx.1.1, ?_⟩
    · exact le_rfl
    rw [hclamp x hx.1.1, inf_eq_left.2 hx.1.2]
    exact hx.2
  · refine le_csInf ⟨b, hab, by rw [hclamp b hab, inf_idem]; exact le_rfl⟩ fun x hx ↦ ?_
    have hxb : x ⊓ b ∈ Icc a b := ⟨le_inf hx.1 hab, inf_le_right⟩
    have hfx : f (x ⊓ b) ≤ x ⊓ b := by
      have := hx.2
      rw [hclamp x hx.1] at this
      exact le_inf this inf_le_right
    have h : lfpIcc f a b ≤ x ⊓ b := csInf_le ⟨a, fun _ hy ↦ hy.1.1⟩ ⟨hxb, hfx⟩
    exact h.trans inf_le_left

-- M9: isFixedPt_clampIcc_iff without MapsTo
theorem M9 (hab : a ≤ b) :
    IsFixedPt (clampIcc f a b) x ↔ x ∈ Icc a b ∧ IsFixedPt f x := by
  constructor
  · intro hx
    have hmem : x ∈ Icc a b := hx.eq ▸ clamp_mem_Icc hab x
    exact ⟨hmem, (clampIcc_eq_of_mem f hmem).symm.trans hx.eq⟩
  · rintro ⟨hmem, hx⟩
    exact (clampIcc_eq_of_mem f hmem).trans hx.eq

-- M10: monotone_clampIcc without `a ≤ b`
theorem M10 (hm : MonotoneOn f (Icc a b)) : Monotone (clampIcc f a b) := fun _ _ hxy ↦
  hm ⟨le_inf le_sup_right le_rfl, inf_le_right⟩ ⟨le_inf le_sup_right le_rfl, inf_le_right⟩
    (inf_le_inf_right _ (sup_le_sup_right hxy _))

-- M11: isFixedPt_prefixedClosure without `x ≤ f x`
theorem M11 (hf : Monotone f) (hbdd : BddAbove (range f)) :
    IsFixedPt f (prefixedClosure f hf hbdd x) := by
  set c := prefixedClosure f hf hbdd
  have h₁ : f (c x) ≤ c x := c.isClosed_closure x
  have h₂ : c x ≤ f (c x) := c.closure_min (hf (c.le_closure x)) (hf h₁)
  exact h₁.antisymm h₂

-- M12: isLeast_prefixedClosure stated as IsGreatest
theorem M12 (hf : Monotone f) (hbdd : BddAbove (range f)) (hx : x ≤ f x) :
    IsGreatest {y | x ≤ y ∧ IsFixedPt f y} (prefixedClosure f hf hbdd x) :=
  ⟨⟨(prefixedClosure f hf hbdd).le_closure x, isFixedPt_prefixedClosure hf hbdd hx⟩,
    fun _ hy ↦ (prefixedClosure f hf hbdd).closure_min hy.1 hy.2.le⟩

-- M13: bridge with gfpIcc on the right
theorem M13 (hab : a ≤ b) (hm : MapsTo f (Icc a b) (Icc a b)) (hf : MonotoneOn f (Icc a b)) :
    letI : Fact (a ≤ b) := ⟨hab⟩
    ((hm.restrictOrderHom hf).lfp : α) = gfpIcc f a b :=
  coe_lfp_restrictOrderHom hab hm hf

-- M16: Route 1B without monotonicity
theorem M16 (hab : a ≤ b) (hb : f b ≤ b) : nextFixedPt f a = lfpIcc f a b := by
  apply le_antisymm
  · exact csInf_le_csInf ⟨a, fun _ hy ↦ hy.1⟩ ⟨b, ⟨hab, le_rfl⟩, hb⟩ fun _ hx ↦ ⟨hx.1.1, hx.2⟩
  · refine le_csInf ⟨b, hab, hb⟩ fun x hx ↦ ?_
    have hxb : a ≤ x ⊓ b := le_inf hx.1 hab
    have hfx : f (x ⊓ b) ≤ x ⊓ b := le_inf (hx.2) hb
    have h : lfpIcc f a b ≤ x ⊓ b := csInf_le ⟨a, fun _ hy ↦ hy.1.1⟩ ⟨⟨hxb, inf_le_right⟩, hfx⟩
    exact h.trans inf_le_left
end

section
variable {α : Type*} [ConditionallyCompleteLinearOrder α] {f : α → α} {a b : α}

-- M6: Route 1A without `f b ≤ b`
theorem M6 (hab : a ≤ b) : nextFixedPt f a = lfpIcc f a b := by
  refine csInf_eq_csInf_of_forall_exists_le (fun x hx ↦ ?_) (fun y hy ↦ ⟨y, ⟨hy.1.1, hy.2⟩, le_rfl⟩)
  rcases le_total x b with hxb | hbx
  · exact ⟨x, ⟨⟨hx.1, hxb⟩, hx.2⟩, le_rfl⟩
  · exact ⟨b, ⟨⟨hab, le_rfl⟩, le_rfl⟩, hbx⟩

-- M7: Route 1A without `a ≤ b`
theorem M7 (hb : f b ≤ b) : nextFixedPt f a = lfpIcc f a b := by
  refine csInf_eq_csInf_of_forall_exists_le (fun x hx ↦ ?_) (fun y hy ↦ ⟨y, ⟨hy.1.1, hy.2⟩, le_rfl⟩)
  rcases le_total x b with hxb | hbx
  · exact ⟨x, ⟨⟨hx.1, hxb⟩, hx.2⟩, le_rfl⟩
  · exact ⟨b, ⟨⟨le_rfl, le_rfl⟩, hb⟩, hbx⟩

-- M17: linear isLeast without `f b ≤ b`
theorem M17 (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a) :
    IsLeast {x ∈ Icc a b | IsFixedPt f x} (nextFixedPt f a) := by
  have hpb : nextFixedPt f a ≤ b := nextFixedPt_le hab le_rfl
  have hap : a ≤ nextFixedPt f a := le_nextFixedPt ⟨b, hab, le_rfl⟩
  have hp : nextFixedPt f a ∈ Icc a b := ⟨hap, hpb⟩
  have h₁ : f (nextFixedPt f a) ≤ nextFixedPt f a := by
    refine le_csInf ⟨b, hab, le_rfl⟩ fun x hx ↦ ?_
    rcases le_total x b with hxb | hbx
    · exact (hm hp ⟨hx.1, hxb⟩ (nextFixedPt_le hx.1 hx.2)).trans hx.2
    · exact (hm hp (right_mem_Icc.2 hab) hpb).trans (hbx)
  have haf : a ≤ f (nextFixedPt f a) := ha.trans (hm (left_mem_Icc.2 hab) hp hap)
  have h₂ : nextFixedPt f a ≤ f (nextFixedPt f a) :=
    nextFixedPt_le haf (hm ⟨haf, h₁.trans hpb⟩ hp h₁)
  exact ⟨⟨hp, h₁.antisymm h₂⟩, fun _ hx ↦ nextFixedPt_le hx.1.1 hx.2.le⟩
end

section
variable {α : Type*} [CompleteLattice α] (f : α →o α)

-- M14: OrderHom.nextFixed_mono with `g ≤ f`
theorem M14 {g : α →o α} (hfg : g ≤ f) {x y : α} (hxy : x ≤ y) (hx : x ≤ f x)
    (hy : y ≤ g y) : (f.nextFixed x hx : α) ≤ (g.nextFixed y hy : α) :=
  OrderHom.lfp.mono (sup_le_sup ((OrderHom.const α).mono hxy) hfg)

-- M15: iterate bound reversed
theorem M15 (n : ℕ) : f.lfp ≤ (⇑f)^[n] ⊥ := by
  induction n with
  | zero => exact bot_le
  | succ n ih => rw [Function.iterate_succ_apply']; exact (f.mono ih).trans_eq f.map_lfp
end
