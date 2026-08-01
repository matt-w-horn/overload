# Queueing/

The classical queueing inputs, stated at the interface the loop consumes.

- `Little.lean`: Stidham's deterministic sample-path `L = λW` and
  Brumelle's weighted `H = λG` on the same sandwich; no `Overload`
  imports.
- `MM1.lean`: M/M/1 mean-value theory (the utilization law `L = ρ/(1-ρ)`
  from balance equations with uniqueness; `W = 1/(μ-λ)` through the
  documented Little bridge), then `mm1Loop` built from the sojourn-tail
  kernel.
- `Erlang.lean`: the Erlang-B loss law; the stable recursion equals the
  closed form, and the blocking kernel is a loop instance.
