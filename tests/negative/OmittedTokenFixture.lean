import Overload.AxiomAudit

/-!
Negative fixture: this file MUST FAIL to elaborate. The declaration name
below carries the omitted-result token `exitTime`, so `#omitted_audit
Overload` must reject it — the deliberately-omitted result families stay
absent by machine check, not only by prose. The test driver (`lake test`)
asserts the rejection (and its exact reason); this file is deliberately
not imported by any build root, so the token never enters a green build.
-/

def Overload.NegativeFixtures.exitTimeProbe : Nat := 0

#omitted_audit Overload
