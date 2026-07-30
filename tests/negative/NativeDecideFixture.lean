import Overload.AxiomAudit

/-!
Negative fixture: this file MUST FAIL to elaborate. The declaration below
closes by `native_decide`, which at this toolchain pin introduces a
per-declaration trust axiom (its name carries `native_decide.ax`) that is
outside the axiom budget; `#axiom_budget_all Overload` must reject it.
The test driver (`lake test`) asserts the rejection (and its exact
reason); this file is deliberately not imported by any build root.
-/

theorem Overload.NegativeFixtures.nativeProbe : 2 + 2 = 4 := by native_decide

#axiom_budget_all Overload
