# OverloadTest/

The test tooling, outside the audited `Overload` namespace.

- `Coverage.lean`: the coverage classifier (bridged, pinned, witnessed,
  consumed, terminal) over the library's dependency graph.
- `Gate.lean`: `#coverage_report`, elaborated at build over the whole
  library. It fails on any uncovered declaration.
- `Ledger.lean`: the two hand-maintained coverage ledgers.
  `terminalLedger` records declarations that are deliberately unconsumed,
  each with a justification; `bridgedLedger` pairs a declaration with the
  theorem proving it equivalent to an independent formulation.
- `Main.lean`: the `lake test` driver: the statement lock, the negative
  fixtures, the scanner corpus, the claims-ledger stages, and the
  import-roots and directory-layer checks.
