#!/usr/bin/env python3
"""The claims ledger's only writer, and its shape validator.

`tests/claims.lock` records one verdict per declaration: that a blinded
referee compared the docstring against the elaborated statement
(`supported`), or that Matt overruled a referee (`accepted`, note
required). The test driver's claims gate compares the ledger's hashes
against the manifest and fails on missing, stale, or orphan rows; it never
writes. All writes go through `record` here, which copies the three hashes
from `.verify/manifest.json` — the hashes are computed only in Lean
(`OverloadTest/Main.lean`), so this script re-implements nothing.

Usage: claims.py check
       claims.py record NAME (supported|accepted) [--note TEXT]

Row format, sorted by name, one per line:
    name | statementHash | docHash | contextHash | verdict | date [| note]
"""
import argparse
import datetime
import json
import sys
from pathlib import Path

LOCK = Path("tests/claims.lock")
MANIFEST = Path(".verify/manifest.json")
MODES = ("advisory", "failing")
VERDICTS = ("supported", "accepted")

HEADER = """-- Claims ledger: one verdict per declaration, written only by
-- scripts/claims.py after a blinded docstring-vs-statement review
-- (design: overload-paper/source/claims-review-design.md). The claims
-- gate in `lake test` compares the hashes below against the manifest;
-- editing a statement, a docstring, or a direct dependency's docstring
-- invalidates the row. In `failing` mode a missing or stale row fails
-- the build; `advisory` prints findings only (pre-bootstrap).
mode: {mode}
"""


def parse(text):
    """Return (mode, rows) or raise ValueError with every defect listed."""
    mode, rows, errors = None, {}, []
    for i, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("--"):
            continue
        if line.startswith("mode:"):
            mode = line.split(":", 1)[1].strip()
            if mode not in MODES:
                errors.append(f"line {i}: mode `{mode}` not in {MODES}")
            continue
        parts = [p.strip() for p in line.split("|")]
        if len(parts) not in (6, 7):
            errors.append(f"line {i}: {len(parts)} fields, want 6 or 7")
            continue
        name, sh, dh, ch, verdict, date = parts[:6]
        note = parts[6] if len(parts) == 7 else None
        if verdict not in VERDICTS:
            errors.append(f"line {i}: verdict `{verdict}` not in {VERDICTS}")
        if verdict == "accepted" and not note:
            errors.append(f"line {i}: `accepted` requires a note")
        if name in rows:
            errors.append(f"line {i}: duplicate row for {name}")
        rows[name] = (sh, dh, ch, verdict, date, note)
    if mode is None:
        errors.append("no `mode:` line")
    names = list(rows)
    if names != sorted(names):
        errors.append("rows are not sorted by name")
    if errors:
        raise ValueError("\n".join(errors))
    return mode, rows


def render(mode, rows):
    lines = [HEADER.format(mode=mode).rstrip(), ""]
    for name in sorted(rows):
        sh, dh, ch, verdict, date, note = rows[name]
        row = f"{name} | {sh} | {dh} | {ch} | {verdict} | {date}"
        if note:
            row += f" | {note}"
        lines.append(row)
    return "\n".join(lines) + "\n"


def cmd_check():
    if not LOCK.exists():
        sys.exit(f"claims: {LOCK} missing")
    try:
        mode, rows = parse(LOCK.read_text())
    except ValueError as e:
        sys.exit(f"claims: {LOCK} malformed:\n{e}")
    print(f"claims: {len(rows)} row(s), mode {mode}, shape ok")


def cmd_record(name, verdict, note):
    if verdict == "accepted" and not note:
        sys.exit("claims: `accepted` requires --note (the recorded override)")
    if not MANIFEST.exists():
        sys.exit(f"claims: {MANIFEST} missing; run `lake exe overloadTest` first")
    manifest = {r["name"]: r for r in json.loads(MANIFEST.read_text())}
    row = manifest.get(name)
    if row is None:
        sys.exit(f"claims: {name} is not in the manifest")
    mode, rows = (
        parse(LOCK.read_text()) if LOCK.exists() else ("advisory", {})
    )
    date = datetime.date.today().isoformat()
    rows[name] = (
        row["statementHash"], row["docHash"], row["contextHash"],
        verdict, date, note,
    )
    LOCK.write_text(render(mode, rows))
    print(f"claims: recorded {verdict} for {name} ({date})")


def main():
    ap = argparse.ArgumentParser(prog="claims.py")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("check")
    rec = sub.add_parser("record")
    rec.add_argument("name")
    rec.add_argument("verdict", choices=VERDICTS)
    rec.add_argument("--note")
    args = ap.parse_args()
    if args.cmd == "check":
        cmd_check()
    else:
        cmd_record(args.name, args.verdict, args.note)


if __name__ == "__main__":
    main()
