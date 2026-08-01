module

public import Overload.Basic -- shake: keep
public import Overload.Loop.ClosedLoop
public import Overload.Capacity.Conservation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

/-!
# Example: thrashing — the phase diagram on an operating system

Memory overcommit in a demand-paged OS, the classic non-distributed
instance of this library's phase diagram. The mapping:

* **Offered load** = multiprogramming level: resident working-set demand
  `Λ` against memory capacity `M` (stylized units: working-set slots).
* **The load-coupled kernel** = the fault storm: below `M`, working sets
  fit and faults are rare, while at and above `M` every quantum faults —
  `stepKernel M`, the saturated cartoon (a fault-rate curve is the
  `mm1Kernel`-style refinement).
* **Retries** = fault-driven re-execution: a faulting quantum is retried
  after paging, up to a cap (here 4 — the stylized number of times a
  quantum re-runs before its page set stabilizes).
* **The waste channel / M4** = paging overhead: CPU spent moving pages is
  capacity that produces no goodput — the waste channel and the
  supply-degradation mechanism in one (`thrashingAcct`,
  `thrashing_waste_caps_goodput`).
* **The classic fix** = multiprogramming-level control: suspending
  processes to keep resident demand clamped is *literally* the clamp
  theorem (`thrashing_mpl_control`) — the 1970s working-set/MPL
  discipline (Denning-era reading), rediscovered by every generation as
  "shed load to escape thrashing".

Honest scope: numbers are stylized illustrations. No page-replacement
policy, no locality model, no fault-rate curve is formalized. The claims
are about the structure (bistability, the clamp, the waste accounting),
which is exactly what transfers from the distributed-systems reading.
-/

@[expose] public section

namespace Overload

/-- The thrashing loop: working-set demand 6 against memory capacity 20,
fault-retry cap 4. -/
noncomputable abbrev thrashingLoop : ClosedLoop :=
  cappedLoop 6 20 4 (by norm_num) (by norm_num)

/-- The congested-side inflow at saturation, shared by the bistability and
equilibrium certificates: `F(20) = 6·4 = 24 ≥ 20`. -/
theorem thrashing_inflow : (20 : ℝ) ≤ thrashingLoop.F 20 := by
  rw [cappedLoop_F_of_ge (by norm_num)]
  norm_num

/-- **Thrashing is bistable.** Working-set demand 6 against memory
capacity 20 with fault-retry cap 4: the healthy state (everything
resident, `F = 6`) coexists with a congested state (`F(20) = 24 ≥ 20` —
fault storms sustain themselves once memory saturates). -/
theorem thrashing_bistable : BistableOn thrashingLoop.F 0 24 := by
  refine thrashingLoop.bistableOn_of_two_points (x := 6) (y := 20)
    (by norm_num) ?_ thrashing_inflow (by norm_num) ?_
  · rw [cappedLoop_F_of_lt (by norm_num)]
  · change (6 : ℝ) * ((4 : ℕ) : ℝ) ≤ 24
    norm_num

/-- The congested (thrashing) state is a genuine equilibrium — a fixed
point at or above capacity (here `F(24) = 24`) — by the inflow
certificate. -/
theorem thrashing_congestedEq : thrashingLoop.CongestedEq 20 :=
  thrashingLoop.congestedEq_of_inflow thrashing_inflow

/-- **Multiprogramming-level control is the clamp theorem.** Suspending
processes down to resident demand 3 (with the same fault-retry cap 4)
removes the thrashing equilibrium outright: `3·4 = 12 < 20`. The classic
working-set/MPL fix, as one inequality. -/
theorem thrashing_mpl_control :
    ¬(cappedLoop 3 20 4 (by norm_num) (by norm_num)).CongestedEq 20 :=
  cappedLoop_no_congestedEq (by norm_num)

/-- Work accounting for a thrashing window: 100 CPU units over the window,
40 useful, 45 destroyed as paging overhead, 15 idle (I/O stalls). Paging
is the waste channel *and* the supply degradation: the CPU the storm eats
is the CPU that otherwise retires work. -/
noncomputable def thrashingAcct : Accounting where
  capacity := 100
  time := 1
  useful := 40
  wasted := 45
  idle := 15
  capacity_pos := by norm_num
  time_pos := by norm_num
  useful_nonneg := by norm_num
  wasted_nonneg := by norm_num
  idle_nonneg := by norm_num
  conserve := by norm_num

/-- Paging waste prices the throughput cliff: with 45% of CPU spent paging
and 15% idle waiting on the disk, useful throughput is capped at 55% of
capacity less the idle share — 40, per `goodput_le_of_waste`. Each point of
paging overhead is a point off the top, and stalling for the pager costs
again. Disclosed: the accounting is fully specified, so the ceiling
coincides with its own `useful` figure; the decomposition is what
transfers. -/
theorem thrashing_waste_caps_goodput {G : ℝ}
    (huseful : G * thrashingAcct.time * 1 ≤ thrashingAcct.useful) :
    G * 1 ≤ (1 - 45 / 100) * thrashingAcct.capacity
      - thrashingAcct.idle / thrashingAcct.time :=
  thrashingAcct.goodput_le_of_waste huseful (by unfold thrashingAcct; norm_num)

end Overload
