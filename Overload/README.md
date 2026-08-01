# Overload/

This directory holds the library, grouped into subject directories in
Mathlib's style. The
layering is a property of the import graph, machine-checked by the
`dir-layers` stage of `lake test`: no import runs backwards through

    Retry -> Capacity -> Loop -> {Queueing, Stack} -> {Dynamics, Control}
          -> Verification -> Examples

Each directory has its own README. Three modules sit at the top level,
outside the order: `Basic.lean` (the shared root import), `Lint.lean`
(registers the enabled theorem-docstring linter), and `AxiomAudit.lean`
(the build-time axiom audit over every declaration in the namespace).
