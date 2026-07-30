import Overload.AxiomAudit

/-!
Negative fixture: this file MUST FAIL to elaborate. The declaration below
uses `sorry`, so it depends on `sorryAx`, and the structural sweep
`#axiom_budget_all Overload` must reject it. The test driver (`lake test`)
asserts the rejection (and its exact reason); this file is deliberately
not imported by any build root.
-/

theorem Overload.NegativeFixtures.sorryProbe : 1 + 1 = 2 := by sorry

#axiom_budget_all Overload
