# Migrating Overload from `lfpIcc`/`gfpIcc` to `nextFixedPt`/`prevFixedPt`

Status: a plan, not applied. Written 2026-11-08 against Overload branch
`claude/knaster-tarski-intervals-a64p1u` after the two refactor commits
("Route every lfpIcc/gfpIcc fixed-point fact through mathlib's OrderHom.lfp" and
"Ceiling-free hysteresis"). The target definitions are those of the Mathlib candidate file
`Mathlib/Order/ConditionallyCompleteLattice/FixedPoints.lean` on the fork branch of the same name.

## The mapping

| Today | After | Hypotheses that disappear | Hypotheses that appear |
| --- | --- | --- | --- |
| `lfpIcc F 0 b` | `nextFixedPt F 0` | `hab : 0 ≤ b`, `MapsTo F (Icc 0 b) (Icc 0 b)`, `MonotoneOn F (Icc 0 b)` | `MonotoneOn F (Ici 0)` (Overload already has it: `ClosedLoop.F_monotoneOn`), `0 ≤ F 0` (`F_nonneg le_rfl`), `∃ b, 0 ≤ b ∧ F b ≤ b` (witness `L.lam * L.Amax` via `F_le`) |
| `gfpIcc F 0 b` | `prevFixedPt F b` | `hab`, `MapsTo`, `MonotoneOn F (Icc 0 b)` | `MonotoneOn F (Iic b)` — **Overload does not have this** (see "Not mechanical" 1), `F b ≤ b` (`F_le`), `∃ a, a ≤ b ∧ a ≤ F a` (witness `0`) |
| `isFixedPt_lfpIcc hab hm hf` | `isFixedPt_nextFixedPt hm' h0 ⟨b, hb0, hFb⟩` | | |
| `lfpIcc_mem_Icc hab hf` | `le_nextFixedPt ⟨b, …⟩` for `0 ≤`, `nextFixedPt_le hb0 hFb` for `≤ b` | | |
| `lfpIcc_le hx hFx` | `nextFixedPt_le hx.1 hFx` | membership `x ≤ b` | |
| `le_gfpIcc hy hyF` | `le_prevFixedPt hy.2 hyF` | membership `0 ≤ y` | |
| `lfpIcc_le_lfpIcc hab hg h` / `lfpIcc_le_lfpIcc_of_le …` | `nextFixedPt_mono le_rfl h ⟨b, …⟩` | `hab`, `MapsTo g`, the ceiling arguments | the pointwise bound only on `Ici 0` |
| `gfpIcc_le_gfpIcc …` / `gfpIcc_le_gfpIcc_of_le …` | `prevFixedPt_mono hb h ⟨0, …⟩` | | |
| `iterate_le_lfpIcc hab hm hf n` | `iterate_le_nextFixedPt hm' h0 ⟨b, …⟩ n` | | |
| `lfpIcc_le_gfpIcc hab hm hf` | `nextFixedPt_le_prevFixedPt hm' h0 hb0 hFb` | | |

The anchor `0` and the ceiling `L.lam * L.Amax` stop being arguments of the equilibrium; the
ceiling survives only inside the existential hypothesis, which `F_le` discharges once.

## Per-file counts (occurrences of `lfpIcc`/`gfpIcc`, after the two refactor commits)

| File | Occurrences | Mechanical? |
| --- | --- | --- |
| `Overload/Loop/Hysteresis.lean` | 85 | mostly; see "Not mechanical" 2 |
| `Overload/Loop/Operator.lean` | 28 | yes (`BistableOn`, certificates, `exists_fixedPt_le/ge`, the two `_of_le` lemmas become `nextFixedPt_mono`/`prevFixedPt_mono` instances) |
| `Overload/Loop/ClosedLoop.lean` | 15 | yes (`congestedEq_of_inflow`, `not_bistableOn_of_const`) |
| `Overload/Loop/Universality.lean` | 7 | yes |
| `Overload/Dynamics/Calculus.lean` | 5 | yes for the five lines; see "Not mechanical" 3 for the continuity theorems |
| `Overload/Examples/SQS.lean` | 1 | docstring mention only |
| `Upstream/Order/FixedPointsIcc.lean` | 55 | file is deleted or moved under `Overload/` (see "Not mechanical" 4) |
| total | 196 | |

`Overload/Control/Autoscaling.lean`, `Overload/Dynamics/Burst.lean`, `Overload/Loop/Eligibility.lean`
contain no occurrence (the brief's line numbers for them are stale); `Burst.lean:122` uses
`exists_fixedPt_ge`, which keeps its statement.

## Not mechanical

1. **The congested equilibrium needs monotonicity below the ceiling.** `prevFixedPt F b` is a
   fixed point when `F` is monotone on `Iic b` (`isGreatest_prevFixedPt`). Overload has
   `MonotoneOn L.F (Ici 0)` and nothing below `0`. Two ways out, both one lemma:
   (a) use the primed form `nextFixedPt_le_prevFixedPt'`-style statements that only need
   `MonotoneOn F (Icc 0 b)` through the Mathlib candidate's clamp lemmas
   (`monotone_comp_clampIcc`, `isFixedPt_comp_clampIcc_iff`), i.e. work with
   `prevFixedPt (fun x ↦ F ((x ⊔ 0) ⊓ b)) b`; or (b) keep `gfpIcc F 0 b` for the congested side
   and migrate only the healthy side. (b) is the smaller change and keeps the asymmetry honest:
   the congested equilibrium genuinely depends on the ceiling (raising `b` can create a new,
   higher congested equilibrium), the healthy one does not.
2. **Closed forms on `stepLoop`** (`stepLoop_lfpIcc_of_lt`, `stepLoop_gfpIcc_of_ge`,
   `stepLoop_gfpIcc_of_healthyOnly`, `stepLoop_lfpIcc_of_ge`, `stepLoop_jump_up/down`,
   `stepLoop_equilibrium_trichotomy`, `stepLoop_sweep_up_le`, and the pins) carry the ceiling
   `lam * A` in their statements. After migration the healthy-side statements read
   `nextFixedPt (stepLoop lam C A _ _).F 0 = lam`; their proofs use `lam_le_F` and the fixed-point
   property and transfer line by line. The congested-side statements depend on item 1.
3. **`Calculus.lean`'s four continuity theorems** (`ContinuousOn F (Icc a b)` at lines ~176, 220,
   248, 833) are about `Icc a b` with general `a`, not about `0`. They should stay on `lfpIcc`
   or, if `lfpIcc` is deleted, be restated with `nextFixedPt F a` under `MonotoneOn F (Ici a)`,
   which they do not currently assume. Keep `lfpIcc` here unless those statements are revisited.
4. **`Upstream/Order/FixedPointsIcc.lean` is no longer upstream-bound.** If PR #42225 is closed
   in favour of the `nextFixedPt` file, `lfpIcc`/`gfpIcc` become Overload's own definitions
   and the file belongs under `Overload/Order/` with its `README.md` row removed. The bridge
   `coe_lfp_restrictOrderHom` and `isLeast_lfpIcc` (now in that file) are what make this cheap:
   every fixed-point fact already routes through Mathlib's `OrderHom.lfp`.
5. **`BistableOn F a b := lfpIcc F a b < gfpIcc F a b`** is a definition in `Operator.lean`;
   changing it changes its statement hash in `tests/statements.lock` and every consumer's
   claims-ledger row. Budget one `--update-lock` and one claims-review wave for it.

## Order of work, if the migration is done

1. Vendor the Mathlib candidate file as `Upstream/Order/ConditionallyCompleteLattice/FixedPoints.lean`
   (or depend on the merged Mathlib).
2. Add Overload-side glue in `ClosedLoop.lean`: `F_prefixed_envelope : ∃ b, 0 ≤ b ∧ L.F b ≤ b`
   and `healthyEq L := nextFixedPt L.F 0`; keep `congestedEq`/`gfpIcc` per item 1(b).
3. Migrate `Operator.lean`, then `ClosedLoop.lean`, `Universality.lean`, then `Hysteresis.lean`
   healthy side. Rebuild after each file (`lake build --wfail`, 33 s).
4. `lake exe overloadTest --update-lock`; claims review for the changed rows; `make verify`.
