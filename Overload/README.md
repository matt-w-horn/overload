# Overload/

This directory holds the library, grouped into subject directories in
Mathlib's style. The layering is a property of the import graph,
machine-checked by the `dir-layers` stage of `lake test`, which reads the
total order `dirOrder` and fails on any import running backwards through

    Retry -> Capacity -> Loop -> Queueing -> Stack -> Dynamics
          -> Control -> Verification -> Examples

Each directory has its own README. Three modules sit at the top level,
outside the order: `Basic.lean` (the shared root import), `Lint.lean`
(registers enabled copies of two Batteries linters, `docBlameThm` and
`explicitVarsOfIff`), and `AxiomAudit.lean` (the build-time axiom audit over
every
declaration in the namespace).
