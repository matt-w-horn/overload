# Queueing/

The classical queueing inputs, stated at the interface the loop consumes.

- `Little.lean`: Stidham's deterministic sample-path `L = λW` and
  Brumelle's weighted `H = λG` on the same sandwich. The module has no
  `Overload` imports.
- `MM1.lean`: M/M/1 mean-value theory, then `mm1Loop` built from the
  sojourn-tail kernel. The utilization law `L = ρ/(1-ρ)` comes from
  balance equations with uniqueness, and `W = 1/(μ-λ)` comes through the
  documented Little bridge.
- `Erlang.lean`: the Erlang-B loss law. The stable recursion equals the
  closed form, and the blocking kernel is a loop instance.
