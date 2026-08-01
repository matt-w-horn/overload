# Control/

The operational levers, each read against the loop.

- `Breaker.lean`: the circuit breaker's open state as a clamp
  (`breakerLoop`); trip and settle dynamics stay omitted.
- `Autoscaling.lean`: certify at the scaled-in floor; capacity enters the
  loop twice, and safety is monotone in both entries.
- `Priority.lean`: undiscriminating contention, and strict priority from
  intent labels.
- `Discipline.lean`: the interface every allocation language implements,
  with strict priority and FIFO's attempts-proportional as its two
  instances, and the FIFO stale-service theorem.
- `Observability.lean`: instruments factoring through lossy labels.
