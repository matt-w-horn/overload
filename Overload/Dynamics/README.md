# Dynamics/

The derivative and trigger readings of the loop.

- `Calculus.lean`: amplification sensitivity, loop gain by the chain
  rule, the two slope flags, the smooth loop `smoothLoop`, and the fluid
  drift, decay, and drain results. ODE solution existence stays omitted,
  and trajectories enter as hypotheses.
- `Burst.lean`: deterministic trigger arithmetic. A cohort of `B`
  released over a window `w` adds `B/w`, and both the safe window and the
  crossing burst are sized off the basin gap.
