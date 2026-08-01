# tests/negative/

Eleven expected-failure fixtures, run by `lake test`, in two classes.

Six must fail to elaborate: `SorryFixture`, `PrivateSorryFixture`,
`NativeDecideFixture`, `OmittedTokenFixture`, `CoverageFixture` (an
unconsumed, unledgered theorem the coverage gate must reject), and
`SilencingMarkersFixture` (one declaration per gate-silencing marker —
`unsafe`, `partial`, `implemented_by`, `extern`, `nolint` — that the
`silencingMarkers` environment linter must flag; its in-file `#lint` run
is what fails elaboration).

Five compile with at most a warning, and the source-level proof-token
scan must reject them instead: `ExampleSorryFixture`,
`StringSorryFixture`, `SorryAxFixture`, `StopFixture`, and
`NativePlusFixture`. Lean adds no `example` to the environment, so
elaboration-time gates cannot see these. The scanner is what rejects
them, and these fixtures are what keep the scanner honest.
