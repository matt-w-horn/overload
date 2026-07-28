/-! Positive corpus for the proof-token scanner: every declaration here is a
hazard shape — a token word buried where it is not a proof token — and the
scanner must report zero findings on this file. The file must also elaborate,
so the shapes are real Lean, not strawmen. The converse cases (tokens the
scanner MUST catch) live in `tests/negative/`. -/

/-- A docstring line shaped like a declaration, ending in the token:
theorem fake_decl : False := sorry
and prose naming sorry, admit, and native_decide directly. -/
def sorryFreeCount : Nat := 0

-- Line comment carrying all three: sorry admit native_decide

/- Block comment with sorry,
   /- a nested block with admit -/
   and text after the nested close. -/
def afterBlockComment : Nat := sorryFreeCount

/-- `--` inside a string literal is content, not a comment opener; nothing on
this line may be hidden from the scanner (the negative fixture
`StringSorryFixture.lean` pins the dangerous half of this case). -/
def dashString : String := "a -- b"

/-- Token words as identifier substrings must not match. -/
def admitsNothing (unsorryLike : Nat) : Nat := unsorryLike

-- Widened-pattern lookalikes in a comment: sorryAx stop +native

/-- Lookalikes for the widened pattern: `sorryAx` and `stop` as identifier
substrings, and `native` after a `+` only as a prefix of a longer word —
none may match. -/
def sorryAxiom (stopped : Nat) : Nat := stopped

/-- `+ native…` where the word continues past `native` is arithmetic, not a
`decide` config flag. -/
def unstoppable (nativeish : Nat) : Nat := nativeish + nativeish
