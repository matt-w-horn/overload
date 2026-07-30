import Lean

/-!
# Coverage ledgers

The two hand-maintained inputs to `#coverage_report` (OverloadTest/Coverage.lean).
Both are honesty surfaces: an entry asserts something the graph cannot see, and
the report throws when an entry goes stale (a terminal entry that gains a
consumer, witness, or pin; a name that no longer exists; a bridge whose theorem
does not depend on its target), so the ledgers cannot silently rot.
-/

namespace OverloadTest

/-- Declarations that are deliverables or pins consumed by nothing: the library
proves them *for the reader* (billed in a prose surface) or *about a
definition* (a sanity, range, eval, or reduction pin), not for another proof.
Each entry carries a one-line justification; "billed in X" names the prose
surfaces citing it. An entry that becomes consumed, witnessed, or pinned fails
the report — delete the entry, the coverage got stronger.

The 2026-07-26 pinning campaign converted every entry that had an honest
numeric pin. What remains is the residue it ruled unpinnable, and each
justification below says which of the three reasons applies: the statement is
`rfl` at a definition, so a consuming pin restates it; the statement
quantifies over a certificate predicate, so a pin supplies a predicate rather
than numbers; or the declaration is a witness already. -/
def terminalLedger : List (Lean.Name × String) :=
  [
    (`Overload.BoundedLoop.withKernel_Amax, "surgery pin: withKernel leaves Amax unchanged; rfl at the definition, so a consuming pin restates it"),
    (`Overload.BoundedLoop.withKernel_F, "surgery pin: the operator after withKernel; rfl at the definition, so a consuming pin restates it"),
    (`Overload.BoundedLoop.withKernel_h, "surgery pin: withKernel leaves the response unchanged; rfl at the definition, so a consuming pin restates it"),
    (`Overload.BoundedLoop.withKernel_lam, "surgery pin: withKernel leaves the offered load unchanged; rfl at the definition, so a consuming pin restates it"),
    (`Overload.ClosedLoop.withLam_Amax, "surgery pin: withLam leaves Amax unchanged; rfl at the definition, so a consuming pin restates it"),
    (`Overload.ClosedLoop.withLam_F, "surgery pin: the operator after withLam; rfl at the definition, so a consuming pin restates it"),
    (`Overload.ClosedLoop.withLam_g, "surgery pin: withLam leaves the kernel unchanged; rfl at the definition, so a consuming pin restates it"),
    (`Overload.ClosedLoop.withLam_h, "surgery pin: withLam leaves the response unchanged; rfl at the definition, so a consuming pin restates it"),
    (`Overload.ClosedLoop.withLam_lam, "surgery pin: withLam sets exactly the offered load; rfl at the definition, so a consuming pin restates it"),
    (`Overload.Star.gain_unique_eq, "uniqueness leg of the star linearization; quantifies over the rank-one factors, and the numbers are already in starWitness"),
    (`Overload.coupledAmp_nil, "base-case eval pin of the load-coupled recursion; rfl at the definition, so a consuming pin restates it"),
    (`Overload.docBlameThmEnabled, "enabled registration of Batteries' docBlameThm; consumed by runLinter through the env_linter attribute at lint time, not by any proof"),
    (`Overload.explicitVarsOfIffEnabled, "enabled registration of Batteries' explicitVarsOfIff; consumed by runLinter through the env_linter attribute at lint time, not by any proof"),
    (`Overload.fluid_decay_witness, "satisfiability witness for fluid_decay_of_deriv_le's eight-hypothesis bundle, with the bound attained at F = 0; already a witness, nothing left to pin"),
    (`Overload.invokeFail_nil, "base-case eval pin of the load-coupled recursion; rfl at the definition, so a consuming pin restates it"),
    (`Overload.signature_gap_witnessed, "terminal deliverable; billed in README; quantifies over the certificate predicate, so a pin supplies a predicate rather than numbers"),
    (`Overload.signature_not_decide_congestedEq_three, "numeric leg of the incompleteness theorem, congestion form; still quantifies over the certificate predicate, so a pin supplies a predicate rather than numbers"),
    (`Overload.signature_not_decide_two_fixedPts_three, "numeric leg of the incompleteness theorem, phase form; still quantifies over the certificate predicate, so a pin supplies a predicate rather than numbers"),
    (`Overload.star_signature_not_decide_congestedEq, "terminal deliverable; billed in README; quantifies over the certificate predicate, so a pin supplies a predicate rather than numbers"),
  ]

/-- Pairs `(target, bridge)`: `bridge` proves `target` equivalent to (or
consistent with) an independent formulation, so `target` is verified beyond
its own statement. The report checks that `bridge` actually depends on
`target`. -/
def bridgedLedger : List (Lean.Name × Lean.Name) :=
  [-- `expAttempts_eq_div` was the original bridge; deleted 2026-07-26 when
    -- `docs/rules.md` moved to citing Mathlib's `geom_sum_eq` directly.
    -- `one_sub_mul_expAttempts` carries the same independent content
    -- (Mathlib's `mul_neg_geom_sum`) without the division.
    (`Overload.expAttempts, `Overload.one_sub_mul_expAttempts),
    (`Overload.lfpIcc, `Overload.lfpIcc_eq_lfp_restrict),
    (`Overload.gfpIcc, `Overload.gfpIcc_eq_gfp_restrict),
    (`Overload.erlangB, `Overload.erlangB_eq_closed),
    (`Overload.propDiscipline, `Overload.propDiscipline_alloc_eq_sharedGoodput),
    -- `meanQueue`'s bridge is the tsum evaluation against Mathlib's geometric
    -- first moment (`meanQueue_eq`), not `meanWait_eq_of_little`, whose
    -- hypothesis states the target in terms of itself (audited 2026-07-26).
    (`Overload.meanQueue, `Overload.meanQueue_eq),
    (`Overload.SamplePath.brumelle, `Overload.SamplePath.little_of_brumelle),
    -- `global_balance` is NOT a bridge for `stationaryWeight`: both sides
    -- unfold the same definition (audited 2026-07-26). It is pinned by
    -- `global_balance_pin`; the independent verification is uniqueness below.
    (`Overload.stationaryWeight, `Overload.stationaryWeight_unique_of_global_balance),
    (`Overload.FactorsThroughSignature, `Overload.factorsThroughSignature_iff),
    (`Overload.BistableBand, `Overload.bistableBand_iff_edges)]

end OverloadTest
