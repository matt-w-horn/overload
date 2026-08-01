import Overload.Lint
import Batteries.Tactic.Lint

/-!
Fixture for the `silencingMarkers` environment linter (`Overload/Lint.lean`):
one declaration per marker the linter must flag — `unsafe`, `partial`, an
`implemented_by` replacement, an `extern` implementation, and a `nolint`
exemption, plus the `private unsafe` spelling — and the in-file `#lint` run
that must reject them. Every declaration elaborates cleanly on its own; the
linter, not the elaborator, carries the rejection. This file pins the firing
side; the real library pins the silent side on every `lake lint`.
-/

/-- Probe: the unsafe marker. -/
unsafe def probeUnsafe : Nat := 0

/-- Probe: the partial marker (opaque constant with a compiler companion). -/
partial def probePartial (n : Nat) : Nat := probePartial n

/-- Replacement target for the probe below; itself unmarked. -/
def probeImpl : Nat → Nat := fun _ => 0

/-- Probe: compiled code replaced by `probeImpl`. -/
@[implemented_by probeImpl] def probeImplementedBy : Nat → Nat := fun _ => 0

/-- Probe: an extern implementation the kernel never checks. -/
@[extern "probe_no_such_symbol"] def probeExtern (n : Nat) : Nat := n

/-- Probe: a lint exemption. -/
@[nolint docBlame] def probeNolint : Nat := 0

/-- Probe: the private spelling must not hide the marker. -/
private unsafe def probePrivateUnsafe : Nat := 0

open Overload in
#lint only silencingMarkers
