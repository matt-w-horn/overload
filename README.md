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
| `lake test` | The statement lock, the claims ledger, the linter-coverage check, the negative fixtures, and the source scans. |
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
