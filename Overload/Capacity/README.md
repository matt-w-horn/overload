# Capacity/

Work conservation at the bottleneck.

- `Conservation.lean`: the accounting frame `C·T = U + W + I`
  (`Accounting`), the scheme-agnostic goodput bound, and the
  concurrency-pool rate bound.
- `Plateau.lean`: the plateau theorem at uniform-loss equilibria, and
  cliff implies waste.
- `Resources.lean`: multi-resource request paths. Hops see full
  amplification, and the binding resource can shift.
