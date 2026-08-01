# tests/

- `statements.lock`: the statement freeze: every declaration's elaborated
  type, with value hashes for definition kinds. Only
  `lake exe overloadTest --update-lock` regenerates it.
- `claims.lock`: docstring-vs-statement verdicts with the hashes they
  were judged at.
- `negative/`: expected-failure fixtures. Five must fail to elaborate.
  The other five compile, and the proof-token scan must reject them.
- `positive/`: `ScannerCorpus.lean`, hazard shapes the scanner must
  produce zero findings on.
- `claims-calibration/`: constructed defective docstring pairs with an
  answer key, for calibrating referees.
