# tests/

- `statements.lock`: the statement freeze; every declaration's elaborated
  type, with value hashes for definition kinds. Regenerated only by
  `lake exe overloadTest --update-lock`.
- `claims.lock`: docstring-vs-statement verdicts with the hashes they
  were judged at.
- `negative/`: expected-failure fixtures; five that must fail to
  elaborate and five that compile and must be rejected by the
  proof-token scan.
- `positive/`: `ScannerCorpus.lean`, hazard shapes the scanner must
  produce zero findings on.
- `claims-calibration/`: constructed defective docstring pairs with an
  answer key, for calibrating referees.
