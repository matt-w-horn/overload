import Overload
import OverloadTest.Coverage

/-!
# The coverage gate

Elaborating this file runs the coverage report over the whole library, so
`lake test` (which builds the test driver, which imports this) fails on any
uncovered declaration. The class tally lands in the build log next to the
axiom audit's count.
-/

#coverage_report Overload
