# Stack/

Composition across layers and across sites.

- `Coupling.lean`: multi-site stability via positive weight certificates
  `J·w < w`, no eigenvalues; the 2-site iff and the k-site row-sum and
  headroom forms.
- `Scheme.lean`: the scheme-agnostic `(trigger, stop, timing, scope)`
  formalism; its quantitative content is one amplification number.
- `CoupledStack.lean`: the composite whose amplification responds to the
  bottom failure level; its two-layer instance is bistable.
- `Tightness.lean`: the converse that makes the clamp condition complete
  over the kernel family.
- `Star.lean`: the fan-in assume-guarantee contract over a shared sink,
  and the signature-sum incompleteness carried over from
  `Loop/Signature.lean`.
