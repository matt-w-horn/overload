import KT.D2
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Basic

/-! # D6 (optional): the orbit supremum `⨆ n, f^[n] a` and when it is the least fixed point. -/

open Filter Topology Set
open Function (IsFixedPt)

namespace KT

section Order

variable {α : Type*} [ConditionallyCompleteLinearOrder α] {f : α → α} {a b : α}

noncomputable def orbitSup (f : α → α) (a : α) : α := ⨆ n, f^[n] a

theorem mapsTo_Icc_of_le_of_le (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a)
    (hb : f b ≤ b) : MapsTo f (Icc a b) (Icc a b) := fun _x hx ↦
  ⟨ha.trans (hm (left_mem_Icc.2 hab) hx hx.1), (hm hx (right_mem_Icc.2 hab) hx.2).trans hb⟩

theorem iterate_mem_Icc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a) (hb : f b ≤ b)
    (n : ℕ) : f^[n] a ∈ Icc a b :=
  (mapsTo_Icc_of_le_of_le hab hm ha hb).iterate n (left_mem_Icc.2 hab)

theorem monotone_iterate (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a) (hb : f b ≤ b) :
    Monotone fun n ↦ f^[n] a := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' f (n + 1)]
    exact hm (iterate_mem_Icc hab hm ha hb n) (iterate_mem_Icc hab hm ha hb (n + 1)) ih

theorem iterate_le_nextFixedPt_of_Icc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a)
    (hb : f b ≤ b) (n : ℕ) : f^[n] a ≤ nextFixedPt f a := by
  obtain ⟨⟨hp, hfix⟩, -⟩ := isLeast_nextFixedPt_of_linear hab hm ha hb
  induction n with
  | zero => exact hp.1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hm (iterate_mem_Icc hab hm ha hb n) hp ih).trans_eq hfix.eq

theorem orbitSup_mem_Icc (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a) (hb : f b ≤ b) :
    orbitSup f a ∈ Icc a b :=
  ⟨le_ciSup_of_le ⟨b, by rintro _ ⟨n, rfl⟩; exact (iterate_mem_Icc hab hm ha hb n).2⟩ 0 le_rfl,
    ciSup_le fun n ↦ (iterate_mem_Icc hab hm ha hb n).2⟩

/-- Unconditional: the orbit supremum is at most the least fixed point above `a`. -/
theorem orbitSup_le_nextFixedPt (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a)
    (hb : f b ≤ b) : orbitSup f a ≤ nextFixedPt f a :=
  ciSup_le fun n ↦ iterate_le_nextFixedPt_of_Icc hab hm ha hb n

end Order

section Topology

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  {f : α → α} {a b : α}

theorem tendsto_iterate_orbitSup (hab : a ≤ b) (hm : MonotoneOn f (Icc a b)) (ha : a ≤ f a)
    (hb : f b ≤ b) : Tendsto (fun n ↦ f^[n] a) atTop (𝓝 (orbitSup f a)) :=
  tendsto_atTop_ciSup (monotone_iterate hab hm ha hb)
    ⟨b, by rintro _ ⟨n, rfl⟩; exact (iterate_mem_Icc hab hm ha hb n).2⟩

theorem isFixedPt_orbitSup_of_continuousOn (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (ha : a ≤ f a) (hb : f b ≤ b) (hf : ContinuousOn f (Icc a b)) : IsFixedPt f (orbitSup f a) := by
  have hL := tendsto_iterate_orbitSup hab hm ha hb
  have hmem := orbitSup_mem_Icc hab hm ha hb
  have h₁ : Tendsto (fun n ↦ f (f^[n] a)) atTop (𝓝 (f (orbitSup f a))) :=
    (hf.continuousWithinAt hmem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hL, Eventually.of_forall (iterate_mem_Icc hab hm ha hb)⟩)
  have h₂ : Tendsto (fun n ↦ f (f^[n] a)) atTop (𝓝 (orbitSup f a)) := by
    simpa only [← Function.iterate_succ_apply'] using (tendsto_add_atTop_iff_nat 1).2 hL
  exact tendsto_nhds_unique h₁ h₂

/-- Under continuity, the orbit supremum is the least fixed point above `a`. -/
theorem orbitSup_eq_nextFixedPt_of_continuousOn (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (ha : a ≤ f a) (hb : f b ≤ b) (hf : ContinuousOn f (Icc a b)) :
    orbitSup f a = nextFixedPt f a :=
  (orbitSup_le_nextFixedPt hab hm ha hb).antisymm <|
    (isLeast_nextFixedPt_of_linear hab hm ha hb).2
      ⟨orbitSup_mem_Icc hab hm ha hb, isFixedPt_orbitSup_of_continuousOn hab hm ha hb hf⟩

end Topology

end KT
