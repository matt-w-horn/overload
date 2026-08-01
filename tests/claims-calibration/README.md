# Referee calibration pairs

Fifteen (statement, docstring) pairs with an answer key. A referee
configuration (model + effort + protocol) must produce the `expected`
verdict on every pair before its verdicts on real pairs are accepted.
The defective pairs must come back with the keyed verdict, the known-good
pairs must come back `supported`, and the ambiguous pair must come back
`intent-unclear`. A confident wrong answer there disqualifies the
configuration as surely as a miss.

Composition, chosen to span the library's shapes (theorem/def kinds,
dependency-bearing statements, every verdict class and axis the schema
names):

- **pair1–pair5** — constructed defects: dropped hypothesis, direction
  flip, unquantified "exactly", vacuous statement under honest prose, and
  an extra clause the statement never states (pair5, re-keyed 2026-07-30
  from intent-unclear after all four calibrated configurations read it,
  defensibly, as prose-overclaims).
- **pair6–pair8** — known-good pairs from documented Mathlib lemmas
  (statements verified against the local pin). They calibrate the
  false-positive direction.
- **pair9–pair11** — constructed defects on the axes the first five
  missed: quantifier overclaim, strength underclaim, and a trivial (not
  vacuous) statement whose docstring bills the inert hypothesis.
- **pair12–pair13** — `def`-kind pairs: an honest body restatement, and a
  docstring claiming a property no definition can assert.
- **pair14** — dependency-bearing: the dispatcher supplies the `deps`
  entries as the per-pair block's verified dependency docstrings. The
  referee must reconstruct the named definition from them in probes.
- **pair15** — the ambiguous pair: prose describing a different provable
  result altogether, so the defect cannot be localized from the pair.

The dispatcher feeds referees only `name`, `kind`, `statement`,
`docstring`, and (where present) `deps`. The `expected`, `axis`, and
`why` fields are the answer key, and they never leave this directory.
Names are styled like real declarations so that a referee cannot
recognize a calibration run. Statements are over plain Mathlib
vocabulary, probe-able through `scripts/claim-probe.sh`. Every
mathematical claim in a `why` field was probe-verified when the pair was
written.
