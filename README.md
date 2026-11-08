# Overload

[![ci](https://github.com/matt-w-horn/overload/actions/workflows/ci.yml/badge.svg)](https://github.com/matt-w-horn/overload/actions/workflows/ci.yml)
![license: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue)

Overload is machine-checked mathematics of retry amplification and
congestion collapse over fixed capacity. It is a Lean 4 + Mathlib library
with zero `sorry` and zero custom axioms. The build fails if either claim
stops being true.

The plateau theorem is the headline. At a uniform-loss equilibrium,
goodput equals `min (∑ lam) C` — independent of the retry caps, and of
every backoff schedule. Under zero-cost rejection and always-useful
processing, retries cannot dent throughput.

```lean
theorem plateau (hcap : ∀ j ∈ s, 1 ≤ cap j) (hlam : ∀ j ∈ s, 0 ≤ lam j)
    {p : ℝ} (heq : UniformLossEq s lam cap C p) :
    goodput s lam cap p = min (∑ j ∈ s, lam j) C
```

`Overload/Capacity/Plateau.lean`. Three more, with the hypotheses they do
and do not need:

- **The clamp theorem** (`Loop/ClosedLoop.lean`): an amplification clamp
  `h ≤ K` with `λ·K < Θ` removes every congested equilibrium — no timing,
  backoff, latency or kernel-shape hypotheses, and no monotonicity.
  Budgets, attempt caps and an open circuit breaker destroy the congested
  equilibrium instead of resisting entry to it.
- **Cliff ⟹ waste** (`Capacity/Plateau.lean`): if waste-discounted goodput
  falls below the plateau, the discount is strictly positive. What it rules
  out is the alternative explanation — that retries or caps moved the
  plateau.
- **Little's law, deterministic sample-path form** (`Queueing/Little.lean`):
  one trace and two rate hypotheses. No distributions, no independence, no
  ergodicity, no order on departures.

## Build and verify

```sh
git clone https://github.com/matt-w-horn/overload
cd overload
brew install elan-init   # once; any elan install works
lake exe cache get       # prebuilt Mathlib binaries
lake build               # library + examples + axiom audit
make verify              # every gate, then a stamp of the verified tree
```

`make verify` is the entry point: it runs everything below and promotes
warnings to failures. The individual targets are listed for when a gate
fails and you want to re-run just that one.

| Target | What it checks |
|---|---|
| `lake build` | The structural axiom audit, as part of the default target. Every module elaborates under Mathlib's standard syntax linter set. |
| `lake test` | The statement lock, the claims ledger (`failing` mode), the linter-coverage check, the negative fixtures, and the source scans. |
| `lake lint` | The environment linters — Batteries' set, plus this library's own `silencingMarkers`, which fails on any library declaration carrying a gate-silencing marker (`unsafe`, `partial`, an `implemented_by` or `extern` replacement, a `nolint` exemption). |
| `lake exe lint-style` | The text-based linters. |

Two kernel re-checks sit behind the build, wired to run weekly in CI and
on demand. `make leanchecker` replays every module through the
toolchain's own checker — the same kernel implementation, at the same
pin, that built the oleans. Imports are trusted, so it catches
elaborator drift, not kernel bugs. `make nanoda` is the independent
watcher.
[lean4export](https://github.com/leanprover/lean4export) writes the
library's full dependency cone, Mathlib included, and
[Nanoda](https://github.com/ammkrn/nanoda_lib), a Lean kernel written
from scratch in Rust, re-checks it declaration by declaration. Axiom
discipline stays with the build-time audit; the second kernel
contributes independent type-checking.

The case for a second implementation: a kernel bug replays
identically in the kernel's own checker, so an independent
implementation would have to be wrong in the same way at the same time
to hide it. That argument is Leonardo de Moura's, in
[Who Watches the Provers?](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/)

## Upstream

Parts of this library have been contributed to mathlib. The library uses
the mathlib versions, and its own older formulations are deleted. Status
as of 2026-11-07:

| Piece | mathlib PR | Status | Copy under `Upstream/` | Used by |
|---|---|---|---|---|
| `sum_range_mul_geometric_add`: the summation-by-parts identity behind the mean of a censored geometric distribution | [#42380](https://github.com/leanprover-community/mathlib4/pull/42380) | merged, used from the mathlib pin | none | `Overload/Retry/AttemptDist.lean` |
| `lfpIcc`, `gfpIcc`: the least and greatest fixed points of a monotone self-map of an interval | [#42225](https://github.com/leanprover-community/mathlib4/pull/42225) | open | `Order/FixedPointsIcc.lean` | `Overload/Loop/Operator.lean` |
| `Real.erlangB`: Erlang's loss formula by its stable recursion, with its bounds and monotonicity | [#42382](https://github.com/leanprover-community/mathlib4/pull/42382) | open | `Analysis/SpecialFunctions/ErlangB.lean` | `Overload/Queueing/Erlang.lean` |
| `tendsto_count_div_atTop` and two companions: the growth rate of a counting function | [#42384](https://github.com/leanprover-community/mathlib4/pull/42384) | open | `Analysis/SpecificLimits/Counting.lean` | `Overload/Queueing/Little.lean` |
| `geometricCensoredMeasure`: the geometric distribution censored at a cap | [#42381](https://github.com/leanprover-community/mathlib4/pull/42381) | open | `Probability/Distributions/GeometricCensored.lean` | `Overload/Retry/AttemptDist.lean` |
| `geometricMeasure_Iio`, `geometricMeasure_Ici`: the head and tail masses of the geometric distribution | [#45786](https://github.com/leanprover-community/mathlib4/pull/45786) | open | `Probability/Distributions/Geometric.lean` | `GeometricCensored.lean` above |

Until a pull request merges, `Upstream/` holds a copy of it, so the
library can use the mathlib formulation before a mathlib release carries
it. Each file sits at its mathlib path with `Mathlib/` replaced by
`Upstream/`, so module `Upstream.X` is the future `Mathlib.X`, and the
declaration names, namespaces, and signatures are mathlib's.

A copy keeps only the declarations the `Overload` library reaches,
directly or through another kept declaration's proof. The kept
declarations are verbatim except where noted below, and each module
docstring drops the lines that name what was cut. The cuts and changes:

- `Order/FixedPointsIcc.lean`: `isLeast_lfpIcc` and its generated dual
  `isGreatest_gfpIcc` are cut.
- `Analysis/SpecialFunctions/ErlangB.lean`: `Real.erlangB_mul_sum` and
  `Real.erlangB_eq_div` (the closed form) are cut, with the three imports
  only they needed. Three proofs also differ: `erlangB_nonneg`,
  `erlangB_denom_pos`, and `erlangB_le_one` pass to `linarith` the facts
  #42382 states as `have` lines, because this library's
  `linter.unusedVariables.analyzeTactics` counts a `have` that only
  `linarith` consumes as unused. The statements are verbatim.
- `Probability/Distributions/Geometric.lean`: holds only the two lemmas
  #45786 adds to mathlib's existing file of that name. The header,
  imports, and namespace lines around them are new.
- `Probability/Distributions/GeometricCensored.lean`: nothing is cut, but
  it imports `Upstream.Probability.Distributions.Geometric` where #42381
  imports `Mathlib.Probability.Distributions.Geometric`, so that it sees
  those two lemmas.

When a pull request merges and the mathlib pin reaches it, its file under
`Upstream/` is deleted and each `import Upstream.X` becomes
`import Mathlib.X`; nothing else changes. For #45786, `Geometric.lean` is
deleted and the changed import line in `GeometricCensored.lean` is
dropped.

The copies build as the `Upstream` library, outside `Overload/` and its
gates (statement lock, claims ledger, coverage, `lake lint`): they follow
mathlib's conventions, and mathlib review is their gate. The library's own
linter options apply to them. The axiom audit reaches every copied
declaration, because each one is used by an `Overload` declaration that
depends on it.

## History

The library was developed privately before release; this repository's
history was restarted on 2026-07-28.

## Related

- [lean-self-audit-template](https://github.com/matt-w-horn/lean-self-audit-template)
  packages the two-tier honesty-gate design used here (axiom audit,
  statement lock, claims ledger) as a fork-ready template for new
  libraries.
- [lean-skills](https://github.com/matt-w-horn/lean-skills) is the set of
  Claude Code skills this library is built and audited with, including
  the blinded claims-review workflow behind the ledger.

## Security

Report vulnerabilities through GitHub's private vulnerability reporting,
not through public issues; see `SECURITY.md`.

## License

Apache-2.0; see `LICENSE`.

Disclaimer: This is a personal project. The views, code, and opinions
expressed here are my own and do not represent those of my current or past
employers.
