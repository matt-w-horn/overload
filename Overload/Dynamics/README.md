# Dynamics/

The derivative and trigger readings of the loop.

- `Calculus.lean`: amplification sensitivity, loop gain by the chain
  rule, the two slope flags, the smooth loop `smoothLoop`, and the fluid
  drift, decay, and drain results. The general trajectory statements take
  the trajectory as a hypothesis. For `smoothLoop` local existence is
  proved by Picard–Lindelöf (`smoothLoop_exists_trajectory`).
  Uniqueness, extension past the local interval, and existence for any
  other loop are not claimed.
- `Burst.lean`: deterministic trigger arithmetic. A cohort of `B`
  released over a window `w` adds `B/w`, and both the safe window and the
  crossing burst are sized off the basin gap.
