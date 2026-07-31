module

public import Lean
public import Overload
public import OverloadTest.Coverage
public import OverloadTest.Gate

/-!
# The test driver

`lake exe overloadTest` is the runtime half of the test suite (the compile-time
half — axiom audit, coverage gate — runs while the libraries build). Stages:

1. **Manifest**: dump every hand-written declaration under `Overload` —
   qualified name, kind, module, pretty-printed elaborated type, value hash
   for definition kinds, docstring, verification class with consumer and
   pin edges (`computeCoverage`, the gate's own code path) — to
   `.verify/manifest.json`. The types are elaborated, so `variable` binders
   are resolved by construction. Cross-checks over the stamped rows follow:
   class strings recognized, tally summing to the universe, pinnedBy
   non-empty on every C3 row that is not itself a pin root.
2. **Statement lock**: compare the manifest against the tracked
   `tests/statements.lock` and fail on removals, changes, *and additions*.
   `--update-lock` regenerates the lock instead; updating it is a deliberate,
   `git diff`-visible act, never a routine one.
   The comparator self-tests against doctored input on every run.
3. **Import roots**: every module under `Overload/` must be imported by both
   `Overload.lean` and `Overload/AxiomAudit.lean` (the audit sweep only sees
   what it imports). Read with `Lean.parseImports'`, not a regex. The same
   headers then feed two structural checks: **linter coverage**, that every
   module reaches the syntax-linter carrier, and **directory layers**, that
   no import runs backwards through `dirOrder`. Both self-test first.
4. **Negative fixtures**: the expected-failure suite from `tests/negative/`
   — each fixture must be rejected by the gate that owns it, with the
   expected message.
5. **Positive corpus**: `tests/positive/ScannerCorpus.lean` must elaborate
   and produce zero findings from the proof-token scanner.
6. **Prose checks**: the Python docs-sync suite (the proof-token scan over
   the library).

Statement types are printed in a bare context (no open namespaces), so the
output is deterministic for a pinned toolchain.
-/

@[expose] public section

open Lean System OverloadTest

/-- One manifest row. `valueHash?` is set for definition kinds only: theorem
proof bodies are deliberately free, definition bodies are part of the meaning
(`Coupling.Certificate` once changed body with no header drift reported).
`terminal` marks membership in `OverloadTest.terminalLedger` — the in-code
record that a declaration is deliberately consumed by nothing; downstream
prose checks read it from the manifest instead of treating a markdown
mention as the record.

The three coverage fields make the gate's classification queryable instead
of build-log-only: `cls` is the row's verification class tag
(`CovClass.tag` — `"C4"`/`"C3"`/`"C2"`/`"C1"`/`"T"`), `consumers` the row's
direct consumers that are themselves universe members — direct in the
*collapsed* graph, where a route through an auxiliary (`Foo._proof_1`
using `X`) is one `Foo → X` edge — and, on C3 rows only, `pinnedBy` the
concrete pin roots whose dependency cones contain the row. Both name lists
are sorted; the JSON omits an empty one. An absent `consumers` key is not
"consumed by nothing": a C1 row's only consumers can sit outside the
universe (`overloadOmittedTokens` is consumed by the `#omitted_audit`
elaborator alone), so dead-code arithmetic must read `cls`, never the
consumer list. None of the three enters `lockBlock`: the lock freezes
statements, not the consumption graph around them. -/
structure Entry where
  name : String
  kind : String
  module : String
  type : String
  valueHash? : Option String
  doc? : Option String
  terminal : Bool := false
  cls : String := ""
  consumers : Array String := #[]
  pinnedBy : Array String := #[]

def Entry.toJson (e : Entry) : Json :=
  Json.mkObj <|
    [("name", Json.str e.name), ("kind", Json.str e.kind),
     ("module", Json.str e.module), ("type", Json.str e.type)]
    ++ (match e.valueHash? with | some h => [("valueHash", Json.str h)] | none => [])
    ++ (match e.doc? with | some d => [("doc", Json.str d)] | none => [])
    ++ (if e.terminal then [("terminal", Json.bool true)] else [])
    ++ [("class", Json.str e.cls)]
    ++ (if e.consumers.isEmpty then []
        else [("consumers", Json.arr (e.consumers.map Json.str))])
    ++ (if e.pinnedBy.isEmpty then []
        else [("pinnedBy", Json.arr (e.pinnedBy.map Json.str))])

/-- The lock block for one declaration: a `#### ` header line, the printed
type indented beneath it, and for definition kinds a value-hash line. -/
def Entry.lockBlock (e : Entry) : String :=
  let typeLines := (e.type.splitOn "\n").map ("  " ++ ·)
  let valueLine := match e.valueHash? with
    | some h => ["  value-hash " ++ h]
    | none => []
  String.intercalate "\n" ([s!"#### {e.name} : {e.kind}"] ++ typeLines ++ valueLine)

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quot"
  | .inductInfo _ => if isStructure env n then "structure" else "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"

def hex (h : UInt64) : String :=
  String.ofList (Nat.toDigits 16 h.toNat)

/-- Declarations under the root by `OverloadTest.auditRule` (the shared
copy of `inAuditedNamespace`, in `OverloadTest/Coverage.lean`), printed
alongside the runtime stages; must equal the count `#axiom_budget_all`
prints at build time. -/
def auditCount (env : Environment) (root : Name) : Nat := Id.run do
  let mut k := 0
  for (n, _) in env.constants.toList do
    if auditRule root n then k := k + 1
  return k

/-- Whether the last name component is a compiler-lifted `_proof_N`
auxiliary. The module system's `@[expose] public section` lifts inline
proof terms into named constants of this shape, and a named constant is
atomic, so `pp.proofs` (default false) never elides it: the lock would
print `stepLoop 1 5 4 X._proof_1 …` where it printed `stepLoop 1 5 4 ⋯ ⋯`
before the migration. Worse, the lifted constants are shared, so one
theorem's lock block can name a *different* theorem's `_proof_1` — renaming
that theorem would then report a statement change on a declaration whose
mathematics did not move. `inlineProofAux` substitutes them away before
printing. -/
def isProofAuxName (n : Name) : Bool :=
  match privateToUserName n with
  | .str _ s => s.startsWith "_proof_"
  | _ => false

/-- Replace every `_proof_N` constant in `e` by its definition, recursively,
so the pretty-printer sees an inline proof term and elides it to `⋯` — the
pre-migration lock form, decoupled from the auxiliaries' unstable names.
Fuel-bounded rather than `partial` (the silencing-guard rejects `partial`);
chains are one or two deep in practice, and `manifestEntries` fails loudly
if a `_proof_` name survives to the printed output. -/
def inlineProofAux (env : Environment) (e : Expr) : Expr := go 8 e where
  go : Nat → Expr → Expr
    | 0, e => e
    | fuel + 1, e => e.replace fun
      | .const n us =>
        if isProofAuxName n then
          match env.find? n with
          | some ci =>
            (ci.value? (allowOpaque := true)).map fun v =>
              go fuel (v.instantiateLevelParams ci.levelParams us)
          | none => none
        else none
      | _ => none

/-- Collect and pretty-print the manifest rows for the hand-written
declarations under `root`, sorted by name. Membership is `cov.univ` —
`computeCoverage` applies `OverloadTest.auditRule` (the axiom sweep's rule,
private declarations un-mangled and included) minus the auto-generated and
projection exemptions, so the manifest universe *is* the coverage gate's
universe, by construction rather than by a second copy of the rule. Each
row is stamped with its verification class, its direct in-universe
consumers, and (C3 rows) the pin roots covering it; `pinnedBy` is computed
by walking each pin root's cone once and inverting. -/
def manifestEntries (root : Name) (cov : CoverageReport) : CoreM (Array Entry) := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for n in cov.univ do
    names := names.push n
  names := names.qsort (·.toString < ·.toString)
  -- Invert the dependency edges: `depsOf` holds exactly the universe
  -- members' deps, so `m` consuming `d` puts `m` in `d`'s consumer list —
  -- minus own-prefix credits, the gate's rule (`f.eq_1` using `f` is not
  -- evidence anyone needs `f`).
  let mut consumersOf : NameMap (Array Name) := {}
  for (m, deps) in cov.depsOf do
    for d in deps do
      unless d.isPrefixOf m do
        consumersOf := consumersOf.insert d (((consumersOf.find? d).getD #[]).push m)
  -- Invert the pin cones: one walk per pin root. A pin root's own cone
  -- contains it, so a C3 pin root lists itself.
  let mut pinnedByOf : NameMap (Array Name) := {}
  for r in cov.pinRoots do
    for m in OverloadTest.cone env root cov.univ cov.depsOf [r] do
      pinnedByOf := pinnedByOf.insert m (((pinnedByOf.find? m).getD #[]).push r)
  let sortedStrings (a : Array Name) : Array String :=
    (a.map (·.toString)).qsort (· < ·)
  let mut entries : Array Entry := #[]
  for n in names do
    let some ci := env.find? n | continue
    let type ← Meta.MetaM.run' do
      return (← Meta.ppExpr (inlineProofAux env ci.type)).pretty (width := 100)
    -- A `_proof_` name surviving to the printed form means `inlineProofAux`
    -- ran out of fuel or found no value; fail rather than lock an unstable
    -- name. Hand-written components never start with an underscore, so the
    -- substring cannot occur legitimately.
    if (type.splitOn "._proof_").length != 1 then
      throwError "manifest: `_proof_` auxiliary survived inlining in the type of {n}: {type}"
    let valueHash? ← match ci with
      | .defnInfo d => do
        let v ← Meta.MetaM.run' do
          return (← Meta.ppExpr (inlineProofAux env d.value)).pretty (width := 100)
        if (v.splitOn "._proof_").length != 1 then
          throwError "manifest: `_proof_` auxiliary survived inlining in the value of {n}"
        pure (some (hex v.hash))
      | _ => pure none
    let doc? ← findDocString? env n
    let module := (moduleOf? env n).map (·.toString) |>.getD "<current>"
    let terminal := OverloadTest.terminalLedger.any (·.1 == n)
    let cls := (cov.classOf n).tag
    let consumers := sortedStrings ((consumersOf.find? n).getD #[])
    let pinnedBy :=
      if cls == "C3" then sortedStrings ((pinnedByOf.find? n).getD #[]) else #[]
    entries := entries.push
      { name := n.toString, kind := kindOf env n ci, module, type, valueHash?, doc?,
        terminal, cls, consumers, pinnedBy }
  return entries

/-- Split a lock file into `name ↦ block` (blocks begin at `#### `). -/
def parseLock (text : String) : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  let mut name : Option String := none
  let mut block : Array String := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "#### " then
      if let some k := name then m := m.insert k (String.intercalate "\n" block.toList)
      name := some line
      block := #[line]
    else if name.isSome && !line.isEmpty then
      block := block.push line
  if let some k := name then m := m.insert k (String.intercalate "\n" block.toList)
  return m

/-- Compare current entries against a lock. Returns human-readable findings;
empty means the statements are unchanged. -/
def lockDiff (lock : Std.HashMap String String) (entries : Array Entry) :
    Array String := Id.run do
  let mut findings : Array String := #[]
  let mut current : Std.HashMap String String := {}
  for e in entries do
    let block := e.lockBlock
    let header := (block.splitOn "\n").head!
    current := current.insert header block
    match lock.get? header with
    | none => findings := findings.push s!"added: {e.name} ({e.kind})"
    | some old =>
      if old != block then
        findings := findings.push s!"changed: {e.name} ({e.kind})"
  for (header, _) in lock.toList do
    unless current.contains header do
      findings := findings.push s!"removed: {header.drop 5}"
  return findings.qsort (· < ·)

/-- The comparator must actually see removals, changes, and additions before
it is trusted on the real tree: run it against doctored input every time. -/
def selfTestLock : IO Unit := do
  let a : Entry := { name := "T.a", kind := "theorem", module := "T", type := "1 = 1",
                     valueHash? := none, doc? := none }
  let b : Entry := { name := "T.b", kind := "def", module := "T", type := "Nat",
                     valueHash? := some "ff", doc? := none }
  let lock := parseLock (a.lockBlock ++ "\n" ++ b.lockBlock ++ "\n")
  unless (lockDiff lock #[a, b]).isEmpty do
    throw <| IO.userError "lock self-test: clean compare reported findings"
  let d1 := lockDiff lock #[a]
  unless d1.size == 1 && (d1[0]!.startsWith "removed: T.b") do
    throw <| IO.userError s!"lock self-test: removal not reported: {d1}"
  let d2 := lockDiff lock #[a, { b with type := "Int" }]
  unless d2.size == 1 && (d2[0]!.startsWith "changed: T.b") do
    throw <| IO.userError s!"lock self-test: type change not reported: {d2}"
  let d3 := lockDiff lock #[a, { b with valueHash? := some "00" }]
  unless d3.size == 1 && (d3[0]!.startsWith "changed: T.b") do
    throw <| IO.userError s!"lock self-test: value change not reported: {d3}"
  let d4 := lockDiff lock #[a, b, { a with name := "T.c" }]
  unless d4.size == 1 && (d4[0]!.startsWith "added: T.c") do
    throw <| IO.userError s!"lock self-test: addition not reported: {d4}"

/-- Modules under `Overload/`, from the filesystem. -/
def sourceModules : IO (Array Name) := do
  let files ← FilePath.walkDir "Overload"
  let mut mods : Array Name := #[]
  for f in files do
    if f.extension == some "lean" then
      let parts := f.withExtension "" |>.components
      mods := mods.push (parts.foldl (init := Name.anonymous) .str)
  return mods

def importsOf (file : FilePath) : IO (Array Name) := do
  let header ← parseImports' (← IO.FS.readFile file) file.toString
  return header.imports.map (·.module)

/-- The subject directories of `Overload/`, in dependency order: no import
may flow backwards through this list. Two entries are placed by the DAG
rather than by subject. `Dynamics` follows `Queueing` because `Calculus`
reads the M/M/1 gain, and `Stack` follows `Loop` because `Star` quantifies
over loop signatures. The top-level modules — `Basic`, `Lint`, `AxiomAudit`
— are infrastructure and sit outside the order. -/
def dirOrder : List Name :=
  [`Retry, `Capacity, `Loop, `Queueing, `Stack, `Dynamics, `Control,
   `Verification, `Examples]

/-- The subject directory of a module, if it has one:
`Overload.Loop.ClosedLoop` is in `Loop`, `Overload.Basic` is in none. A
module nested deeper (`Overload.Loop.Sub.Mod`) is still in `Loop` — the
first match was exactly three components, which silently exempted deeper
nesting from the layer check. -/
def dirOf : Name → Option Name
  | m => match m.components with
    | `Overload :: d :: _ :: _ => some d
    | _ => none

/-- Import edges running backwards through `dirOrder`, as human-readable
findings; empty means every edge flows forward. Edges inside one directory
are allowed, and an edge touching a module outside `Overload/`'s
subdirectories — top level, Mathlib, Batteries — is not an edge of this
graph at all. A module in a subject directory that `dirOrder` does not
list is a finding, not an exemption: skipping it silently would exempt
every edge into and out of a new directory nobody added to the order. -/
def layerFindings (edges : Array (Name × Array Name)) : Array String := Id.run do
  let idx (d : Name) : Option Nat := dirOrder.findIdx? (· == d)
  let mut findings : Array String := #[]
  for (m, imps) in edges do
    let some dm := dirOf m | continue
    let some im := idx dm
      | findings := findings.push
          s!"{m} is in directory {dm}, which dirOrder does not list"
        continue
    for i in imps do
      let some di := dirOf i | continue
      let some ii := idx di
        | findings := findings.push
            s!"{m} imports {i}: directory {di} is not listed in dirOrder"
          continue
      if ii > im then
        findings := findings.push
          s!"{m} imports {i}: {di} is later than {dm} in the directory order"
  return findings.qsort (· < ·)

/-- The layer check must actually see a backward edge before its verdict on
the real tree counts: run it against a constructed one every time, the same
discipline as `selfTestLock`. Calibrated 2026-07-29 — reversing `dirOrder`
against the real tree surfaces 52 backward edges, so the check is not
vacuous on this library. -/
def selfTestLayers : IO Unit := do
  let backward : Array (Name × Array Name) :=
    #[(`Overload.Loop.ClosedLoop, #[`Overload.Control.Breaker])]
  let f := layerFindings backward
  unless f.size == 1 && (f[0]!.splitOn "is later than").length > 1 do
    throw <| IO.userError s!"layer self-test: backward edge not reported: {f}"
  -- A deeper-nested module is still in its directory: the check must see
  -- through `Overload.Loop.Sub.Mod`, which an exactly-three-components
  -- `dirOf` silently exempted.
  let nested : Array (Name × Array Name) :=
    #[(`Overload.Loop.Sub.Mod, #[`Overload.Control.Breaker])]
  let n := layerFindings nested
  unless n.size == 1 && (n[0]!.splitOn "is later than").length > 1 do
    throw <| IO.userError s!"layer self-test: nested-module backward edge not reported: {n}"
  -- A directory `dirOrder` does not list is a finding, in both roles:
  -- silently skipping it would exempt every edge touching a new directory
  -- nobody added to the order.
  let unlisted : Array (Name × Array Name) :=
    #[(`Overload.Newdir.Mod, #[]),
      (`Overload.Loop.ClosedLoop, #[`Overload.Newdir.Mod])]
  let u := layerFindings unlisted
  unless u.size == 2 && u.all (fun s => (s.splitOn "dirOrder").length > 1) do
    throw <| IO.userError s!"layer self-test: unlisted directory not reported: {u}"
  -- Forward, same-directory, top-level, and non-Overload edges: all silent.
  let allowed : Array (Name × Array Name) :=
    #[(`Overload.Control.Breaker,
        #[`Overload.Loop.ClosedLoop, `Overload.Control.Priority,
          `Overload.Basic, `Mathlib]),
      (`Overload.Basic, #[`Overload.Control.Breaker])]
  let g := layerFindings allowed
  unless g.isEmpty do
    throw <| IO.userError s!"layer self-test: allowed edges reported: {g}"

/-- Run a process, returning exit code and combined output. -/
def run (cmd : String) (args : Array String) : IO (UInt32 × String) := do
  let out ← IO.Process.output { cmd, args }
  return (out.exitCode, out.stdout ++ out.stderr)

structure Failure where
  stage : String
  detail : String

def negativeFixtures : List (String × String) :=
  [("SorryFixture.lean", "depends on sorryAx"),
   ("PrivateSorryFixture.lean", "privateSorryProbe depends on sorryAx"),
   ("NativeDecideFixture.lean", "._native.native_decide.ax"),
   ("OmittedTokenFixture.lean", "carries the omitted-result token `exitTime`"),
   ("CoverageFixture.lean", "uncovered (C0)")]

def scannerFixtures : List String :=
  ["ExampleSorryFixture.lean", "StringSorryFixture.lean",
   "SorryAxFixture.lean", "StopFixture.lean", "NativePlusFixture.lean"]

unsafe def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update-lock"
  unless (← FilePath.pathExists "Overload.lean") do
    throw <| IO.userError "run from the repo root (Overload.lean not found)"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- `level := .private` is today's default, passed explicitly: the manifest
  -- and audit-rule count must see private declarations, and a default that
  -- moved would silently blind both.
  -- `importAll`, matching `Overload/AxiomAudit.lean`: a plain import resolves
  -- at the exported level, which leaves private declarations out of
  -- `env.constants` entirely. Without it this driver counts a different
  -- universe from the build-time audit (914 against 919 on 2026-07-29, the
  -- gap being declarations the module migration made private).
  let env ← importModules
    #[{module := `Overload, importAll := true},
      {module := `Overload.AxiomAudit, importAll := true}]
    {} (trustLevel := 1024) (loadExts := true) (level := .private)
  let count := auditCount env `Overload
  IO.println s!"overloadTest: environment loaded, audit-rule count {count}"
  let mut failures : Array Failure := #[]

  -- [1] manifest rows, cross-checked BEFORE the file is written: a
  -- stale-ledger tree must not leave a wrong-classed manifest on disk for
  -- the paper repo's scripts, which read .verify/ — on any coverage
  -- failure the file is deleted, so downstream readers fail loudly
  -- instead of reading yesterday's classes.
  let cov := computeCoverage env `Overload
  let ctx : Core.Context := { fileName := "<overloadTest>", fileMap := default }
  let entries ← Prod.fst <$> (manifestEntries `Overload cov).toIO ctx { env }

  -- [1b] coverage cross-checks over the stamped rows. Recomputing the tally
  -- through the same `computeCoverage` would compare a code path with
  -- itself, so the checks here are the ones that catch real drift instead:
  -- ledger findings the build-time gate would have thrown, an unknown or
  -- C0 class string on a row, a C3 row whose pin-cone inversion found no
  -- root (every C3 row sits in some root's cone by construction — a root's
  -- own cone contains it, so roots self-list and an inversion that drops a
  -- root fails here too), a T row with an in-universe consumer (the gate's
  -- staleness check would have thrown first, so this catches a broken
  -- inversion), and a class tally that fails to sum to the universe size.
  let mut covFailures : Array Failure := #[]
  for f in cov.findings do
    covFailures := covFailures.push ⟨"coverage", f⟩
  let mut kc4 := 0; let mut kc3 := 0; let mut kc2 := 0
  let mut kc1 := 0; let mut kt := 0
  for e in entries do
    match e.cls with
    | "C4" => kc4 := kc4 + 1
    | "C3" => kc3 := kc3 + 1
    | "C2" => kc2 := kc2 + 1
    | "C1" => kc1 := kc1 + 1
    | "T" => kt := kt + 1
    | other =>
      covFailures := covFailures.push
        ⟨"coverage", s!"{e.name} carries class `{other}`; the manifest must \
          not ship a C0 or unclassified row"⟩
    if e.cls == "C3" && e.pinnedBy.isEmpty then
      covFailures := covFailures.push
        ⟨"coverage", s!"C3 row {e.name} has empty pinnedBy"⟩
    if e.cls == "T" && !e.consumers.isEmpty then
      covFailures := covFailures.push
        ⟨"coverage", s!"terminal row {e.name} carries in-universe consumers {e.consumers}"⟩
  let ksum := kc4 + kc3 + kc2 + kc1 + kt
  if ksum != cov.univ.size then
    covFailures := covFailures.push
      ⟨"coverage", s!"manifest class tally {ksum} does not sum to universe size {cov.univ.size}"⟩
  IO.FS.createDirAll ".verify"
  if covFailures.isEmpty then
    IO.FS.writeFile ".verify/manifest.json"
      ((Json.arr (entries.map Entry.toJson)).pretty.push '\n')
    IO.println s!"manifest: {entries.size} declarations -> .verify/manifest.json"
  else
    if (← FilePath.pathExists ".verify/manifest.json") then
      IO.FS.removeFile ".verify/manifest.json"
    IO.println "manifest: withheld (coverage cross-checks failed; stale file removed)"
  failures := failures ++ covFailures
  -- The build-time gate prints this same tally from its own environment;
  -- `make tally-sync` compares the two lines, because two printed totals
  -- with no comparison between them are two unchecked numbers (the
  -- 914-vs-919 lesson). Keep the format character-identical to the gate's.
  let pct (k : Nat) : Nat := k * 100 / cov.univ.size
  IO.println s!"manifest-tally: {cov.univ.size} declarations under `Overload` — \
    C4 bridged {kc4} ({pct kc4}%), C3 pinned {kc3} ({pct kc3}%), \
    C2 witnessed {kc2} ({pct kc2}%), C1 consumed {kc1} ({pct kc1}%), \
    terminal {kt} ({pct kt}%), C0 uncovered 0 \
    (exempt auto-generated: {cov.exempt})"

  -- [2] statement lock
  selfTestLock
  let lockFile : FilePath := "tests" / "statements.lock"
  let lockText := String.intercalate "\n\n" (entries.map Entry.lockBlock).toList
  if update then
    IO.FS.writeFile lockFile
      ("-- Statement lock: elaborated types (and definition value hashes) of\n\
        -- every hand-written declaration under `Overload`, printed by\n\
        -- `lake exe overloadTest --update-lock`. Proof bodies of theorems are\n\
        -- deliberately not frozen. A diff in this file is a deliberate\n\
        -- statement-level change, never a routine one.\n\n"
        ++ lockText ++ "\n")
    IO.println s!"lock: wrote {entries.size} blocks to {lockFile}"
  else if (← lockFile.pathExists) then
    let diffs := lockDiff (parseLock (← IO.FS.readFile lockFile)) entries
    if diffs.isEmpty then
      IO.println s!"lock: {entries.size} statements match {lockFile} (self-test ok)"
    else
      for d in diffs do
        failures := failures.push ⟨"lock", d⟩
  else
    failures := failures.push ⟨"lock", s!"{lockFile} missing; run with --update-lock"⟩

  -- [3] import roots. Three hand-maintained lists, same hazard each: a
  -- module missing from one is silently outside that root's sweep.
  -- `OverloadTest/Gate.lean` joined when the coverage report moved there —
  -- its consumption graph only sees modules it `import all`s.
  let mods ← sourceModules
  let rootImports ← importsOf "Overload.lean"
  let auditImports ← importsOf ("Overload" / "AxiomAudit.lean")
  let gateImports ← importsOf ("OverloadTest" / "Gate.lean")
  for m in mods do
    unless rootImports.contains m do
      failures := failures.push ⟨"import-roots", s!"{m} not imported by Overload.lean"⟩
    unless m == `Overload.AxiomAudit || auditImports.contains m do
      failures := failures.push ⟨"import-roots", s!"{m} not imported by Overload/AxiomAudit.lean"⟩
    unless gateImports.contains m do
      failures := failures.push ⟨"import-roots", s!"{m} not imported by OverloadTest/Gate.lean"⟩
  IO.println s!"import-roots: {mods.size} modules checked against three roots"

  -- [3b] linter coverage: syntax linters only run in modules that
  -- transitively import them, so the lakefile's linter options are inert
  -- in any module that does not reach the carrier import (demonstrated
  -- 2026-07-29: `decide +native` in a slim-import module elaborated with
  -- no warning). Every module must reach `Mathlib` wholesale or the
  -- carrier directly, possibly through other Overload modules — the
  -- downstream analogue of Mathlib's `linter.checkInitImports`.
  let carrier := `Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
  let mut directImports : Array (Name × Array Name) := #[]
  for m in mods do
    let path := (System.mkFilePath (m.components.map (·.toString))).addExtension "lean"
    directImports := directImports.push (m, ← importsOf path)
  let mut covered : Std.HashSet Name := {}
  for (m, is) in directImports do
    if is.contains `Mathlib || is.contains carrier then
      covered := covered.insert m
  let mut changed := true
  while changed do
    changed := false
    for (m, is) in directImports do
      if !covered.contains m && is.any (covered.contains ·) then
        covered := covered.insert m
        changed := true
  for m in mods do
    unless covered.contains m do
      failures := failures.push ⟨"linter-coverage",
        s!"{m} does not (transitively) import {carrier}; the syntax linters never run there"⟩
  IO.println s!"linter-coverage: {mods.size} modules checked against the syntax-linter carrier"

  -- [3c] directory layers: the subject directories are ordered and no import
  -- may run backwards through that order. `linter-coverage` above already
  -- read every module's header into `directImports`, so this stage costs one
  -- pass over it. Before the move to subject directories the order was a
  -- claim CLAUDE.md made in prose and nothing checked.
  selfTestLayers
  for d in layerFindings directImports do
    failures := failures.push ⟨"dir-layers", d⟩
  -- Count by `dirOrder` index, not by `dirOf`: an edge touching a directory
  -- the order does not list is reported above, not checked, and counting it
  -- as checked would let the reassuring total mask the skip.
  let ordered (m : Name) : Bool := ((dirOf m).bind fun d => dirOrder.findIdx? (· == d)).isSome
  let layerEdges := directImports.foldl (init := 0) fun k (m, is) =>
    if ordered m then k + (is.filter ordered).size else k
  IO.println s!"dir-layers: {layerEdges} intra-library edges checked against \
    {dirOrder.length} ordered directories (self-test ok)"

  -- [4] negative fixtures
  for (file, expected) in negativeFixtures do
    let (code, out) ← run "lean" #[s!"tests/negative/{file}"]
    if code == 0 then
      failures := failures.push ⟨"negative", s!"{file} elaborated; it must be rejected"⟩
    else if (out.splitOn expected).length > 1 then
      IO.println s!"negative: {file} rejected as expected"
    else
      failures := failures.push
        ⟨"negative", s!"{file} failed without the expected message ({expected}):\n{out}"⟩
  for file in scannerFixtures do
    -- The scanner fixtures' argument rests on their compiling with at most
    -- a warning — that is what makes them invisible to the elaboration
    -- gates. Pin that property: ExampleSorryFixture silently stopped
    -- elaborating once (2026-07-29, an import drift) and nothing noticed,
    -- because only the scanner ever read it.
    let (code, out) ← run "lean" #[s!"tests/negative/{file}"]
    if code != 0 then
      failures := failures.push ⟨"negative",
        s!"{file} no longer elaborates; the scanner, not the elaborator, must reject it:\n{out}"⟩
    let (code, out) ← run "python3"
      #["scripts/checks.py", "--scan", s!"tests/negative/{file}"]
    if code == 0 then
      failures := failures.push
        ⟨"negative", s!"{file} passed the proof-token scan; it must be rejected"⟩
    else
      IO.println s!"negative: {file} rejected by proof-tokens: {out.trimAscii.toString}"

  -- [5] positive corpus
  let corpus := "tests/positive/ScannerCorpus.lean"
  let (code, out) ← run "python3" #["scripts/checks.py", "--scan", corpus]
  if code != 0 then
    failures := failures.push ⟨"positive", s!"scanner false-positive on {corpus}:\n{out}"⟩
  let (code2, out2) ← run "lean" #[corpus]
  if code2 != 0 then
    failures := failures.push ⟨"positive", s!"{corpus} does not elaborate:\n{out2}"⟩
  if code == 0 && code2 == 0 then
    IO.println s!"positive: {corpus} elaborates, zero scanner findings"

  -- [6] prose checks
  let (code, out) ← run "python3" #["scripts/checks.py", "."]
  IO.print out
  if code != 0 then
    failures := failures.push ⟨"prose", "checks.py failed (see output above)"⟩

  if failures.isEmpty then
    IO.println "overloadTest: all runtime stages green"
    return 0
  else
    for f in failures do
      IO.eprintln s!"FAIL [{f.stage}] {f.detail}"
    return 1
