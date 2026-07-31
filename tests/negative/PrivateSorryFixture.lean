import Overload.AxiomAudit

/-!
Negative fixture: this file MUST FAIL to elaborate. The declaration below is
`private`, so it reaches the environment mangled as
`_private.<Module>.<n>.Overload.NegativeFixtures.privateSorryProbe` — a name
whose root is `_private` and which `Lean.Name.isInternal` reports true.

The sweep's original rule, `n.getRoot == root && !n.isInternal`, skipped
exactly that shape: the declaration carries `sorryAx` and the audit printed a
clean count anyway. `inAuditedNamespace` un-mangles with
`Lean.privateToUserName` before testing, which is what this fixture holds
shut.

The hole is small today, because nothing in the library is `private`. It
stops being small under the module system, where every declaration outside a
`public section` is private by default — this fixture is what makes the
migration safe rather than hopeful. The test driver (`lake test`) asserts the
rejection and its exact reason; this file is deliberately not imported by any
build root.
-/

private theorem Overload.NegativeFixtures.privateSorryProbe : 3 + 3 = 6 := by sorry

#axiom_budget_all Overload
