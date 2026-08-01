# Overload

[![ci](https://github.com/matt-w-horn/overload/actions/workflows/ci.yml/badge.svg)](https://github.com/matt-w-horn/overload/actions/workflows/ci.yml)
![license: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue)

Overload is machine-checked mathematics of retry amplification and
congestion collapse over fixed capacity. It is a Lean 4 + Mathlib library
with zero `sorry` and zero custom axioms. The build fails if either claim
stops being true.

## Build

```sh
brew install elan-init   # once; any elan install works
lake exe cache get       # prebuilt Mathlib binaries
lake build               # library + examples + axiom audit
make verify              # every gate, then a stamp of the verified tree
```

`lake build` runs the structural axiom audit as part of the default
target, and it elaborates every module under Mathlib's standard syntax
linter set. `lake test` runs the statement lock, the linter-coverage
check, the negative fixtures, and the source scans. `lake lint` runs the
environment linters, and `lake exe lint-style` runs the text-based ones.
`make verify` runs all of them and promotes warnings to failures.
`make leanchecker` replays every module through the kernel.

## History

This repository's public history begins at its initial commit; the library
was developed privately before release, and its history was restarted on
2026-07-28.

## Related

- [lean-self-audit-template](https://github.com/matt-w-horn/lean-self-audit-template)
  packages the two-tier honesty-gate design used here (axiom audit,
  statement lock, claims ledger) as a fork-ready template for new
  libraries.
- [lean-skills](https://github.com/matt-w-horn/lean-skills) is the set of
  Claude Code skills this library is built and audited with, including
  the blinded claims-review workflow behind the ledger.

## License

Apache-2.0 — see `LICENSE`.

Disclaimer: This is a personal project. The views, code, and opinions
expressed here are my own and do not represent those of my current or past
employers.
