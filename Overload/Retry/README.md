# Retry/

Attempt arithmetic with no feedback loop: what one client's retry policy
does, before load couples to failure. Nothing here imports the loop.
`Loop/` consumes these definitions.

- `Amplification.lean`: the truncated-geometric expected attempt count
  `expAttempts`, defined as the finite geometric sum so that it is total.
  The `(1-p^n)/(1-p)` quotient is a lemma.
- `AttemptDist.lean`: the attempt-count masses form a probability
  distribution on `Fin n`, so `expAttempts` is a genuine expectation.
- `Deadline.lean`: how many attempts fit a deadline (`neff`, via
  `Nat.findGreatest`), plus the re-armed vs remaining-deadline distinction
  and the constant, linear, and geometric backoff levers.
- `Compose.lean`: one-layer downward failure composition (`composeFail`).
- `Composition.lean`: the multiplicative cross-layer composition law and
  its failure conditions, as weighted `Finset` sums.
