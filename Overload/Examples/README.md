# Examples/

Concrete systems entering the theory by instance, one file per system.

- `SQS.lean`: server-side redelivery as a sustaining mechanism. The
  dead-letter queue is the clamp, with its honest residual band.
- `Borg.lean`: priority bands over one cluster, allocation isolation, and
  a per-class loop over allocated capacity.
- `Thrashing.lean`: memory overcommit as the phase diagram.
  Multiprogramming-level control is the clamp theorem.
- `Pipeline.lean`: the honest non-instance. Envelope and waste vocabulary
  transfer, and it asserts no load-coupled kernel.
- `Deficit.lean`: congestion-induced supply degradation as a coupled
  site.
- `Mesh.lean`: two regions by two tiers. Stack budgets feed the spill
  matrix, with the matrix entries disclosed as modeling inputs.
