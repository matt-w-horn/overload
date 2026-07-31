module

-- The syntax-linter carrier; see the note in `Overload/Basic.lean`.
public import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter -- shake: keep
import Mathlib.Tactic.TypeStar

/-!
# Signal fidelity: why a mislabeled instrument hides real harm

Between layers sits a translation map taking downstream outcomes to the code a
layer emits upward. An instrument built on the *wire* label — the
emitted code — sees only what that label preserves. Miscoding (a timeout
emitted as a generic error, an overload as unavailability, a throttle as
spillover) collapses distinct ground-truth states into one wire class, and any
instrument reading that class **cannot** separate them, however the underlying
system differs.

* `instrument_blind` — an instrument factoring through a labeling `wire` is
  constant on `wire`'s fibers: two ground-truth states with the same wire
  label are indistinguishable to it *by construction*. Absence of a signal on
  such an instrument is a property of the instrument, not the system.
* `intent_refines` — carrying failure origin (an `intent` label) alongside
  the wire code separates exactly the states the wire label conflated. This is
  the design prescription (a simulator, or a dashboard, should carry
  ground-truth origin separately from the wire code) stated as a theorem.

This is the mathematics behind a dashboard that shows "no errors" for traffic
that is in fact taking failures: the graph is a function of a lossy label, so
its silence is uninformative about the states that label merges.
-/

@[expose] public section

namespace Overload

variable {State Wire Reading : Type*}

/-- An instrument *factors through* a wire labeling if its reading depends on
the ground-truth state only via that state's wire label. -/
def FactorsThrough (instr : State → Reading) (wire : State → Wire) : Prop :=
  ∃ view : Wire → Reading, ∀ s, instr s = view (wire s)

/-- **Instrument blindness.** If an instrument factors through a wire labeling,
then any two states sharing a wire label produce identical readings. A
dashboard built on the emitted code cannot distinguish states the code
conflates — so its reading (including "no errors") says nothing about which of
those states obtains. -/
theorem instrument_blind {instr : State → Reading} {wire : State → Wire}
    (hfac : FactorsThrough instr wire) {s t : State} (h : wire s = wire t) :
    instr s = instr t := by
  obtain ⟨view, hview⟩ := hfac
  rw [hview s, hview t, h]

/-- The refined labeling that carries failure origin (`intent`) alongside the
wire code. -/
def refinedLabel (wire : State → Wire) (intent : State → Reading) :
    State → Wire × Reading := fun s => (wire s, intent s)

/-- **Intent refinement restores separability.** Two states that the wire
label conflated but that differ in ground-truth origin (`intent`) get distinct
refined labels. Carrying failure origin separately from the wire code — the
design prescription — makes the harm visible again. -/
theorem intent_refines {wire : State → Wire} {intent : State → Reading}
    {s t : State} (hintent : intent s ≠ intent t) :
    refinedLabel wire intent s ≠ refinedLabel wire intent t := by
  intro h
  exact hintent (congrArg Prod.snd h)

/-- The instrument reading the *intent* directly factors through the refined
label — reading the origin is reading part of that label. The complementary
negative, that it does not factor through the wire label whenever two states
share a code but differ in origin, is `instrument_blind` contraposed against
`intent_refines`; it is not this statement's content. -/
theorem intent_factorsThrough_refined {wire : State → Wire}
    (intent : State → Reading) :
    FactorsThrough intent (refinedLabel wire intent) :=
  ⟨Prod.snd, fun _ => rfl⟩

/-- The miscoding pair on concrete labels: two ground-truth states — shed
under overload and a genuine client error — carry the same wire code in a
two-code space, so a dashboard that factors through that code reads `0`
incidents on both (`instrument_blind` at the shared code). The refined
label on the same wire separates them, and the instrument that reads
intent factors through it. -/
theorem miscoded_pair_blind_then_refined :
    (fun _ : Fin 2 => (0 : Fin 2)) 0 = (fun _ : Fin 2 => (0 : Fin 2)) 1 ∧
      (fun _ : Fin 2 => (0 : Nat)) 0 = (fun _ : Fin 2 => (0 : Nat)) 1 ∧
      refinedLabel (fun _ : Fin 2 => (0 : Fin 2)) (fun s => s) 0
        ≠ refinedLabel (fun _ : Fin 2 => (0 : Fin 2)) (fun s => s) 1 ∧
      FactorsThrough (fun s : Fin 2 => s)
        (refinedLabel (fun _ : Fin 2 => (0 : Fin 2)) (fun s => s)) :=
  ⟨rfl,
    instrument_blind (wire := fun _ : Fin 2 => (0 : Fin 2)) (s := 0) (t := 1)
      ⟨fun _ => 0, fun _ => rfl⟩ rfl,
    intent_refines (by decide),
    intent_factorsThrough_refined _⟩

end Overload
