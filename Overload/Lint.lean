module

-- The syntax-linter carrier; see the note in `Overload/Basic.lean`.
public import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter -- shake: keep
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint.Misc

/-!
# Enabled registrations of default-disabled Batteries linters

Batteries defines `docBlameThm` and `explicitVarsOfIff` but registers them
disabled; the registry is keyed by short name, so enabling one takes a new
registration rather than an attribute on the original. The declarations
here are those enabled registrations, picked up by this repo's lint driver
(`lake lint`): every theorem must carry a docstring, and no `↔` statement
may bind a variable explicitly when it appears on both sides.
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
unification from an application of either direction, so it should be
implicit. -/
@[env_linter] def explicitVarsOfIffEnabled : Linter := explicitVarsOfIff

end Overload
