# Overload

Machine-checked mathematics of retry amplification and congestion collapse
over fixed capacity: a Lean 4 + Mathlib library with zero `sorry`, zero
custom axioms, and a build that fails if either claim stops being true.

## Build

```sh
brew install elan-init   # once; any elan install works
lake exe cache get       # prebuilt Mathlib binaries
lake build               # library + examples + axiom audit
make verify              # every gate, then a stamp of the verified tree
```

`lake build` runs the structural axiom audit as part of the default target
and elaborates every module under Mathlib's standard syntax linter set;
`lake test` runs the statement lock, the linter-coverage check, the
negative fixtures, and the source scans; `lake lint` runs the environment
linters, and `lake exe lint-style` the text-based ones. `make verify` runs
all of them with warnings promoted to failures, and `make leanchecker`
replays every module through the kernel.

## History

This repository's public history begins at its initial commit; the library
was developed privately before release, and its history was restarted on
2026-07-28.

## License

Apache-2.0 — see `LICENSE`.

Disclaimer: This is a personal project. The views, code, and opinions
expressed here are my own and do not represent those of my current or past
employers.
