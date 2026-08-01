# scripts/

Checks that read source text rather than the elaborated environment,
plus the claims-review tooling.

- `checks.py`: the proof-token scan that `lake test` shells out to, over
  the library and, with `--scan`, over one fixture at a time.
- `claims.py`: the claims ledger's only writer.
- `claim-probe.sh`: elaborates Lean read from stdin against the built
  library. It is the blinded claims review's one probe command.
- `nolints-style.txt`: the style-lint exception list.
