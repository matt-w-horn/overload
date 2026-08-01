# Loop/

The central object: a closed demand loop over a shared bottleneck, and
its order theory.

- `Operator.lean`: Knaster–Tarski on real intervals (`lfpIcc`, `gfpIcc`),
  the two-point `BistableOn` certificate, and the basin and separatrix
  lemmas.
- `ClosedLoop.lean`: `BoundedLoop` (the boundedness core carrying `F`,
  `CongestedEq`, and the clamp certificates) and `ClosedLoop` (adds
  monotonicity and the `1 ≤ h` floor), with the concrete constructors
  `kernelLoop`, `stepLoop`, and `cappedLoop`.
- `Universality.lean`: phase regions on `(λ, A, C)`; the healthy and
  congested legs are universal over any loop, the bistable leg is
  existential.
- `Hysteresis.lean`: equilibrium selection under a load sweep; collapse
  at the band's upper edge, recovery only at its lower edge.
- `Eligibility.lean`: demand-side miscoding; congestion transfers up the
  response order, and the eligible-mass loop family.
- `Signature.lean`: the contract scalar `σ = λ·Amax` and its
  incompleteness.
