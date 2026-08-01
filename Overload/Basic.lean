module

-- The syntax-linter carrier (Mathlib's `Mathlib.Init` pattern): linters
-- only run in modules that transitively import them, so every module must
-- reach this import or the lakefile's linter options are silently inert
-- there. The test driver's linter-coverage stage enforces the closure.
public import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter -- shake: keep

/-!
# Overload — shared conventions

Overload is a Lean 4 + Mathlib formalization of the equilibrium and
order-theoretic core of overload dynamics: demand, amplification, and
collapse over fixed capacity. Docstrings locate each module in the
library's model hierarchy (levels 0–4, waste accounting, verification
suite, universality groups).

Conventions used throughout the library:

* All rates, probabilities, and capacities live in plain `ℝ`, with explicit
  hypotheses (`0 ≤ p`, `p ≤ 1`, `0 < C`, …) on the theorems that need them.
* Definitions are total. Partiality lives in hypotheses, never in the
  definitions themselves (for example, expected attempts is *defined* as a
  geometric sum, and the `(1 - p^n)/(1 - p)` closed form is a lemma
  requiring `p ≠ 1`).
* Zero `sorry`, zero custom axioms. Results that need unformalized
  analysis (fluid limits, bifurcation geometry, exit times) are omitted,
  not axiomatized. `Overload/AxiomAudit.lean` enforces the axiom budget.
-/

@[expose] public section

namespace Overload

end Overload
