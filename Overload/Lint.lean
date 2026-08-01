module

-- The syntax-linter carrier; see the note in `Overload/Basic.lean`.
public import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter -- shake: keep
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint.Misc
public meta import Lean.Compiler.ImplementedByAttr
public meta import Lean.Compiler.ExternAttr

/-!
# Library-side linter registrations

Batteries defines `docBlameThm` and `explicitVarsOfIff` but registers them
disabled. The registry is keyed by short name, so enabling one takes a new
registration rather than an attribute on the original. The first two
declarations here are those enabled registrations; the third,
`silencingMarkers`, is this library's own linter over the environment-visible
gate-silencing markers. All three are picked up by this repo's lint driver
(`lake lint`). Every theorem must carry a docstring, an `↔` statement must
not bind a variable explicitly when it appears on both sides, and no
declaration may carry a gate-silencing marker.
-/

@[expose] public section

-- Linter registrations run at elaboration time, so under the module system
-- both the import and the declarations are `meta`; the `env_linter`
-- attribute rejects a non-`meta` declaration outright.
meta section

namespace Overload

open Batteries.Tactic.Lint

/-- Batteries' `docBlameThm` linter, re-registered enabled: `lake lint`
fails on any theorem in this library without a docstring. The Batteries
registration is disabled by default and keyed by short name, so enabling
it takes a new registration rather than an attribute on the original. -/
@[env_linter] def docBlameThmEnabled : Linter := docBlameThm

/-- Batteries' `explicitVarsOfIff` linter, re-registered enabled: `lake
lint` fails on any `↔` statement that binds a variable explicitly when it
occurs on both sides of the iff. Such a variable is inferred by
unification from an application of either direction, so it must be
implicit. -/
@[env_linter] def explicitVarsOfIffEnabled : Linter := explicitVarsOfIff

/-- Environment linter over the gate-silencing markers a declaration can
carry: `unsafe` and `partial` (the kernel's consistency and termination
checks are skipped or sidestepped), a compiled-code replacement (the
implemented_by attribute, or an `extern` implementation — the kernel never
checks the replacement, so any downstream native_decide would trust it
unchecked), and a nolint exemption from an environment linter. The
library carries none of these; this linter keeps that a checked fact.
Two markers stay outside its reach, covered at diff time by the Makefile's
silencing-guard: an in-file `set_option` (syntax, invisible to an
environment linter), and a nolint exemption from this linter itself
(Batteries skips an exempted declaration before the test runs). -/
@[env_linter] def silencingMarkers : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No declaration carries a gate-silencing marker."
  errorsFound := "DECLARATIONS CARRY GATE-SILENCING MARKERS:"
  test declName := do
    -- Every recursive definition, structural or not, gets a compiler
    -- companion whose safety reads partial; the companion says nothing
    -- about its parent, so it is skipped, and the parent is judged below.
    if declName matches .str _ "_unsafe_rec" then return none
    let env ← Lean.getEnv
    let mut hits : Array Lean.MessageData := #[]
    if let some info := env.find? declName then
      if info.isUnsafe then
        hits := hits.push m!"marked unsafe"
      if let .defnInfo v := info then
        if v.safety matches .«partial» then
          hits := hits.push m!"marked partial"
      -- A `partial` definition elaborates to an opaque constant whose value
      -- lives only in its `_unsafe_rec` companion; a structural recursion
      -- keeps its value (defnInfo, safe) beside the same companion. The
      -- pair (opaque, companion) is therefore the partial marker.
      if info matches .opaqueInfo _ then
        if (env.find? (.str declName "_unsafe_rec")).isSome then
          hits := hits.push m!"marked partial (opaque with a `_unsafe_rec` companion)"
    if let some impl := Lean.Compiler.getImplementedBy? env declName then
      hits := hits.push m!"compiled code replaced by `{impl}` (implemented_by)"
    if (Lean.getExternAttrData? env declName).isSome then
      hits := hits.push m!"extern implementation"
    if let some ls := nolintAttr.getParam? env declName then
      hits := hits.push m!"lint exemption (nolint {ls})"
    if hits.isEmpty then return none
    return some (Lean.MessageData.joinSep hits.toList m!", ")

end Overload
