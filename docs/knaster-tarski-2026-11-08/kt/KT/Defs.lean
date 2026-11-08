import Mathlib.Order.FixedPoints
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Closure

/-!
# Definitions only

All candidate definitions in one file, so that each equality route can import the
definitions without importing another route's theorems.

* D0 `lfpIcc`/`gfpIcc`: the PR #42225 definitions (copied verbatim, minus `@[expose]`).
* D2 `nextFixedPt`/`prevFixedPt`: anchored infimum of prefixed points above `a`.
* D3 `clampIcc`: `f ∘ clamp` on any lattice.
* D4 `prefixedClosure`: D2 packaged as a `ClosureOperator`.
-/

open Function (IsFixedPt)
open Set

namespace KT

variable {α : Type*} [ConditionallyCompleteLattice α]

/-- D0 (PR #42225). -/
noncomputable def lfpIcc (f : α → α) (a b : α) : α := sInf {x ∈ Icc a b | f x ≤ x}

/-- D0 (PR #42225). -/
noncomputable def gfpIcc (f : α → α) (a b : α) : α := sSup {x ∈ Icc a b | x ≤ f x}

/-- D2: the infimum of the prefixed points of `f` above `a`. -/
noncomputable def nextFixedPt (f : α → α) (a : α) : α := sInf {x | a ≤ x ∧ f x ≤ x}

/-- D2: the supremum of the postfixed points of `f` below `b`. -/
noncomputable def prevFixedPt (f : α → α) (b : α) : α := sSup {x | x ≤ b ∧ x ≤ f x}

/-- D3: `f` precomposed with the lattice clamp onto `Icc a b`. -/
def clampIcc {β : Type*} [Lattice β] (f : β → β) (a b : β) (x : β) : β := f ((x ⊔ a) ⊓ b)

theorem bddBelow_prefixed (f : α → α) (x : α) : BddBelow {y | x ≤ y ∧ f y ≤ y} :=
  ⟨x, fun _ h ↦ h.1⟩

theorem prefixed_nonempty {f : α → α} (hbdd : BddAbove (range f)) (x : α) :
    {y | x ≤ y ∧ f y ≤ y}.Nonempty :=
  let ⟨M, hM⟩ := hbdd
  ⟨x ⊔ M, le_sup_left, (hM (mem_range_self _)).trans le_sup_right⟩

/-- D4: the closure operator `x ↦ sInf {y | x ≤ y ∧ f y ≤ y}` whose closed elements are the
prefixed points of `f`. -/
noncomputable def prefixedClosure (f : α → α) (hf : Monotone f) (hbdd : BddAbove (range f)) :
    ClosureOperator α :=
  ClosureOperator.ofPred (fun x ↦ sInf {y | x ≤ y ∧ f y ≤ y}) (fun y ↦ f y ≤ y)
    (fun x ↦ le_csInf (prefixed_nonempty hbdd x) fun _ hy ↦ hy.1)
    (fun x ↦ le_csInf (prefixed_nonempty hbdd x) fun _ hy ↦
      (hf (csInf_le (bddBelow_prefixed f x) hy)).trans hy.2)
    (fun x _ hxy hy ↦ csInf_le (bddBelow_prefixed f x) ⟨hxy, hy⟩)

end KT
