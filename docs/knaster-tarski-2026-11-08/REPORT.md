# Report: Knaster–Tarski on intervals, Mathlib PR #42225, and Overload

Session 2026-11-08. Everything below was compiled or run in this session against Mathlib
`cdb2d388` (toolchain `leanprover/lean4:v4.36.0-rc2`), the same revision Overload pins.
Working notes with the per-phase evidence: `NOTES.md` next to this file.

## 1. Outcome

**D2 won.** The Mathlib candidate defines `nextFixedPt f a := sInf {x | a ≤ x ∧ f x ≤ x}` and its
dual `prevFixedPt` in a conditionally complete lattice, proves `nextFixedPt f a` is the least fixed
point of `f` above `a` when `f` is monotone on `Set.Ici a`, `a ≤ f a`, and some prefixed point
lies above `a`, and shows it equals Mathlib's `OrderHom.nextFixed` on a complete lattice.
**All six equality routes agree:** under PR #42225's hypotheses, the subtype bridge (D1), the
anchored infimum composed with the clamp (D3∘D2), and the closure operator of the clamp (D4∘D3)
all equal `lfpIcc f a b`, with the model-checked minimal hypotheses confirmed exactly (Route 1A
needs only `a ≤ b`, `f b ≤ b`; Route 1C only `a ≤ b` and `∀ z ∈ Icc a b, f z ≤ b`).
**Overload builds and passes `make verify`** after both refactors (bridge proofs; ceiling-free
hysteresis), with the claims gate switched to advisory as you directed; 13 advisory findings are
open.

Nothing was opened on GitHub. Four Mathlib commits and five Overload commits are pushed to the two
fork branches named `knaster-tarski-intervals`.

## 2. Decisions for Matt

**(a) Which PR to open first.** The fork branch carries three separable commits:
`fe010ef` (PR_A: the new file `Mathlib/Order/ConditionallyCompleteLattice/FixedPoints.lean`,
173 lines), `fc1905c` (PR_B: nine lemmas added to `Mathlib/Order/FixedPoints.lean`), `8b3c7c0`
(PR_C: `Set.MapsTo.restrictOrderHom` in `Mathlib/Order/Hom/Basic.lean`). Each passes
`runLinter` and `lint-style`. Fact that forces the choice: PR_A is the one that answers the
reviewer's comment and replaces #42225; PR_B and PR_C are independent of it and of each other
(PR_A does not use them). Recommendation: open PR_B first (small, complete-lattice-only, no
design question), then PR_A as the rework of #42225, then PR_C only if Overload's bridge is
proposed upstream. Cost of the recommendation: three review threads instead of one.

**(b) Migrate Overload or keep `lfpIcc` with bridge proofs.** Fact: Overload's `F` is monotone
only on `Set.Ici 0` (`ClosedLoop.lean:122`, `:212`), which is exactly `nextFixedPt`'s hypothesis
for the healthy equilibrium but not `prevFixedPt`'s (`Set.Iic b`) for the congested one. So a
full migration is asymmetric: healthy side mechanical (ceiling disappears), congested side either
keeps `gfpIcc` or goes through the clamp. `docs/MIGRATION.md` has the mapping, per-file counts
(196 occurrences after this session's refactors), and five non-mechanical places.
Recommendation: keep `lfpIcc`/`gfpIcc` in Overload now (they are no longer upstream-bound, so
move the file under `Overload/`), and migrate only when the Mathlib file is merged. Cost: the
ceiling stays an argument on the healthy side, though after commit `a970bf0` it no longer forces
a common interval in the hysteresis lemmas.

**(c) Where Lean needed more than the model checker claimed.** Nowhere. Routes 1A and 1C
compile with exactly the model-checked hypotheses. One statement was changed instead:
`nextFixedPt_le_prevFixedPt` is stated with `MonotoneOn f (Ici a)` (brief: `Icc a b`) because the
`Icc` version is provable only through the two-sided interval theorem; that version is compiled
as `nextFixedPt_le_prevFixedPt_of_Icc` in `kt/KT/Agreement.lean`.

**(d) The claims ledger.** Per your instruction the gate is advisory (`mode: advisory` in
`tests/claims.lock`, commit `9318c8f`). Thirteen findings are open: two new lemmas without
verdicts, eight stale rows (statement or docstring or dependency docstring changed), three
orphan rows for deleted declarations. Recording deferrals with `scripts/claims.py record … accepted`
(your 2026-11-07 precedent) was blocked by the permission classifier as a CI bypass; I did not
retry. The orphan rows have no `claims.py` subcommand to remove them.

## 3. Corrected name table

See `NOTES.md`, section "Phase 1". Headline corrections to the brief: `ClosureOperator.ofPred_apply`
and `ofPred_isClosed` exist (simps-generated); `csInf_eq_csInf_of_forall_exists_le` exists but
needs a linear order; `Set.MapsTo.coe_iterate_restrict` exists; `OrderHom.coe_iterate` does not;
`Mathlib/Order/FixedPoints.lean` has no `to_dual` tags, so `OrderHom.nextFixed` statements cannot
be auto-dualized. The brief's Overload call-site lines for `Autoscaling.lean:80`,
`Eligibility.lean:69`, `Burst.lean:112` are stale: those files contain no `lfpIcc`/`gfpIcc`.

## 4. Compiled files

All against Mathlib `cdb2d388`; 0 `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound` only.

| Path | Lines | Linter |
| --- | --- | --- |
| `mathlib4/Mathlib/Order/ConditionallyCompleteLattice/FixedPoints.lean` (PR_A) | 173 | `runLinter` pass, `lint-style` pass |
| `mathlib4/Mathlib/Order/FixedPoints.lean` (PR_B, +54) | — | `runLinter` pass |
| `mathlib4/Mathlib/Order/Hom/Basic.lean` (PR_C, +7) | — | `runLinter` pass |
| `overload/Upstream/Order/FixedPointsIcc.lean` | 199 | Overload `lake lint`, `lint-style` pass |
| `kt/KT/Defs.lean` | 57 | Mathlib standard linter set on, no warnings |
| `kt/KT/D1.lean`, `D2.lean`, `D3.lean`, `D4.lean`, `E.lean`, `D6.lean` | 87, 126, 47, 85, 63, 87 | same |
| `kt/KT/Eq1A.lean`, `Eq1B.lean`, `Eq1C.lean`, `Eq2.lean`, `Eq3.lean`, `Eq4.lean` | 26, 23, 31, 41, 18, 20 | same |
| `kt/KT/Agreement.lean` | 91 | same |
| `lean/Mutants.lean` (17 wrong variants, all fail) | 152 | — |

## 5. Failures, what I did instead, what it cost

- `to_dual` on `OrderHom.coe_nextFixed` failed ("translated type is not type correct") because
  Mathlib's `nextFixed`/`prevFixed` carry no `to_dual` tag. Wrote `coe_prevFixed` by hand (+6 lines).
- Same cause in Overload's vendored file: `iterate_le_lfpIcc`'s `to_dual` failed once
  `isFixedPt_gfpIcc` was hand-written. Tagged the hand-written duals `@[to_dual existing]`.
  Then `--wfail` turned two "redundant `(reorder := a b)`" warnings into errors; removed the
  argument. Cost: two rebuilds.
- Overload `make verify` test stage failed after the hysteresis commit: 8 statement-lock
  differences (expected, statements changed deliberately) and 13 claims findings. Regenerated the
  lock with `lake exe overloadTest --update-lock`. The claims step was then made advisory on
  your instruction. The commit `a970bf0` message records the gate as red at that commit.
- Recording `accepted` verdicts: blocked by the classifier (see 2(d)). Not retried.
- Several `csInf_le`/`⟨…⟩` terms failed to elaborate without an expected type (`Invalid
  projection`); fixed with a named `have` or a helper `bddBelow_prefixed`. Cost: four rebuilds.
- Parallel shell calls that `cd` into different directories ran in the wrong directory twice;
  redone with subshells. No wrong edits resulted.

## 6. Reply to the reviewer: slot structure only (you write it)

1. Concede, one sentence. Say "agreed", not "you're right". Name the collapse: on `Icc a b` with
   `Set.Icc.completeLattice`, `lfpIcc` is `↑(OrderHom.lfp (restriction))` (the bridge is now
   proved in Overload).
2. Past-tense reason, one sentence: endpoints move during parameter sweeps, so `Fact (a ≤ b)`
   and a coercion back to `ℝ` appeared in every statement. No Overload link.
3. What the chain pointed at, one or two sentences: `OrderHom.nextFixed`/`prevFixed` exist only
   for complete lattices; the conditionally complete version ("the least fixed point above `a`",
   `sInf {x | a ≤ x ∧ f x ≤ x}`, hypotheses `MonotoneOn f (Ici a)`, `a ≤ f a`, a prefixed point
   above `a`) seems to be missing, and `Ici a ⊆ ℝ` has no complete lattice structure to apply
   `lfp` to. Name `nextFixed`. Skip the `CompleteSublattice` technicality.
4. Offer, one question: rework #42225 in place to that file, or close it and open fresh. Make
   "close it" cheap. No "to be clear".

## 7. Draft PR descriptions (for you to edit)

**PR_A** — `feat(Order/ConditionallyCompleteLattice): Knaster–Tarski above a point`

> Define `nextFixedPt f a = sInf {x | a ≤ x ∧ f x ≤ x}` and its dual `prevFixedPt f b` in a
> conditionally complete lattice, and prove `isLeast_nextFixedPt`: if `f` is monotone on `Ici a`,
> `a ≤ f a`, and some prefixed point of `f` lies above `a`, then `nextFixedPt f a` is the least
> fixed point of `f` above `a`. On a complete lattice this is `OrderHom.nextFixed`
> (`OrderHom.coe_nextFixed`), so the file is the conditionally complete version of that
> construction; it is the order-theoretic twin of `exists_mem_Icc_isFixedPt`, with the same
> bracket hypotheses and extremality instead of existence. Also monotonicity in the map and the
> anchor (`nextFixedPt_mono`, no monotonicity of the maps needed), orbit bounds, and two clamp
> lemmas turning `MonotoneOn f (Icc a b)` into global monotonicity without changing fixed points
> in `Icc a b`. Reworks #42225 along the lines of the review there.
>
> Assisted-by: Claude Fable 5.1

**PR_B** — `feat(Order/FixedPoints): orbit bounds and monotonicity for nextFixed/prevFixed`

> Add `OrderHom.iterate_bot_le_lfp`, `gfp_le_iterate_top`, `iterate_le_nextFixed`,
> `prevFixed_le_iterate`, `nextFixed_le_of_le`, `le_prevFixed_of_le`, `nextFixed_le_prevFixed`,
> `nextFixed_mono`, `prevFixed_mono`. The existing `nextFixed_le` compares only against fixed
> points; `nextFixed_le_of_le` compares against prefixed points, and `nextFixed_mono` is
> `lfp.mono` specialised to `const x ⊔ f`.
>
> Assisted-by: Claude Fable 5.1

## 8. Not done

- The 165 (now 196) `lfpIcc`/`gfpIcc` occurrences in Overload were not migrated (by design).
- The blinded claims review for the 13 advisory findings.
- `PR_C`'s home: `Set.MapsTo.restrictOrderHom` sits in `Order/Hom/Basic.lean`; a reviewer may
  prefer `Order/Hom/Set.lean`.
- D6 (orbit supremum) is compiled in `kt/KT/D6.lean` but not prepared as a Mathlib file; the
  `ℝ`/`ContinuousOn` convergence theorem `orbitSup_eq_nextFixedPt_of_continuousOn` would be a
  separate small PR into `Topology/Order`, as the brief estimated.
