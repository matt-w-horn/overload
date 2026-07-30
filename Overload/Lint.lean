import Batteries.Tactic.Lint
-- The syntax-linter carrier; see the note in `Overload/Basic.lean`.
import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter -- shake: keep

/-!
# Enabled registrations of default-disabled Batteries linters

Batteries defines `docBlameThm` and `explicitVarsOfIff` but registers them
disabled; the registry is keyed by short name, so enabling one takes a new
registration rather than an attribute on the original. The declarations
here are those enabled registrations, picked up by this repo's lint driver
(`lake lint`): every theorem must carry a docstring, and no `↔` statement
may bind a variable explicitly when it appears on both sides.
-/

namespace Overload

open Batteries.Tactic.Lint

/-- Batteries' `docBlameThm` linter, re-registered enabled: `lake lint`
fails on any theorem in this library without a docstring. The Batteries
registration is disabled by default and keyed by short name, so enabling
it takes a new registration rather than an attribute on the original. -/
@[env_linter] def docBlameThmEnabled : Linter := docBlameThm

/-- Batteries' `explicitVarsOfIff` linter, re-registered enabled: `lake
lint` fails on any `↔` statement that binds a variable explicitly when it
occurs on both sides of the iff. Such a variable cannot be inferred from
an application of either direction, so it should be implicit. -/
@[env_linter] def explicitVarsOfIffEnabled : Linter := explicitVarsOfIff

end Overload
