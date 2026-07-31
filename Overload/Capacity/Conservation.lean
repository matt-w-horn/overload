module

public import Overload.Basic -- shake: keep
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
# Work conservation at the bottleneck

The accounting frame: over an observation window, capacity·time splits
exactly into useful, wasted, and idle work — no mechanism manufactures
capacity. The scheme-agnostic goodput bound `G ≤ min(λ, C/sbar)` follows from
the accounting alone: it holds for *every* retry scheme, backoff policy, and
topology, because none of them appear in the hypotheses.

The `wasted` field aggregates the five waste channels, each separately
measurable in a real system:
1. processed duplicates (retry and hedge races);
2. work completed after caller abandonment (deadline-expired service);
3. queue occupancy ordered against usefulness (stale-first service under
   overload);
4. rejection cost paid downstream of the scarce resource;
5. cancellation latency and failure (signal sent ≠ resource reclaimed).
-/

@[expose] public section

namespace Overload

/-- Work accounting at a bottleneck over an observation window. Units: `capacity`
is work per unit time, `useful`/`wasted`/`idle` are work totals over the window. -/
structure Accounting where
  /-- Bottleneck capacity, work per unit time. -/
  capacity : ℝ
  /-- Length of the observation window. -/
  time : ℝ
  /-- Work that produced goodput. -/
  useful : ℝ
  /-- Work that produced nothing a caller kept (the five waste channels). -/
  wasted : ℝ
  /-- Capacity left unused. -/
  idle : ℝ
  /-- Capacity is positive. -/
  capacity_pos : 0 < capacity
  /-- The observation window has positive length. -/
  time_pos : 0 < time
  /-- Useful work is nonnegative. -/
  useful_nonneg : 0 ≤ useful
  /-- Wasted work is nonnegative. -/
  wasted_nonneg : 0 ≤ wasted
  /-- Idle work is nonnegative. -/
  idle_nonneg : 0 ≤ idle
  /-- Conservation: the bottleneck neither manufactures nor destroys capacity. -/
  conserve : useful + wasted + idle = capacity * time

namespace Accounting

variable (A : Accounting)

/-- Useful work is at most capacity·time: conservation with the nonnegative
`wasted` and `idle` terms dropped. -/
theorem useful_le : A.useful ≤ A.capacity * A.time := by
  linarith [A.conserve, A.wasted_nonneg, A.idle_nonneg]

/-- **The scheme-agnostic goodput bound** `G ≤ min(λ, C/sbar)`: goodput `G` is
bounded by offered load and by capacity over per-request service demand. The
hypotheses mention no retry scheme, no backoff, no topology — the bound holds
for all of them. -/
theorem goodput_le {G sbar lam : ℝ} (hs : 0 < sbar)
    (huseful : G * A.time * sbar ≤ A.useful) (hoffered : G ≤ lam) :
    G ≤ min lam (A.capacity / sbar) := by
  refine le_min hoffered ?_
  rw [le_div_iff₀ hs]
  nlinarith [A.useful_le, A.time_pos]

/-- Waste and idleness together cap goodput: if a fraction `w` of
capacity·time is wasted, then `G·sbar ≤ (1-w)·C - I/T`. Both subtractions are
sharp — the conclusion is the useful-work hypothesis re-expressed through
conservation, with `wasted` and `idle` named instead of `useful`. That is
the whole content: the waste fraction relabels the ceiling, it does not
tighten it, so a statement dropping the idle term (`G·sbar ≤ (1-w)·C`) would
be strictly weaker than its own hypothesis. The point of the decomposition
is that `w` is separately measurable channel by channel, which `useful`
is not. -/
theorem goodput_le_of_waste {G sbar w : ℝ}
    (huseful : G * A.time * sbar ≤ A.useful)
    (hw : A.wasted = w * (A.capacity * A.time)) :
    G * sbar ≤ (1 - w) * A.capacity - A.idle / A.time := by
  have hT : 0 < A.time := A.time_pos
  refine le_of_mul_le_mul_right ?_ hT
  have hexp : ((1 - w) * A.capacity - A.idle / A.time) * A.time
      = (1 - w) * (A.capacity * A.time) - A.idle := by
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hT)]
    ring
  rw [hexp]
  nlinarith [A.conserve, hw, huseful]

end Accounting

/-- **Concurrency pools bound throughput**: with time-averaged
in-flight equal to rate times sojourn (Little's identity, supplied as a
hypothesis — the same interface stance as the suite's `little` field), a
pool of `P` slots over sojourn `s` admits at most `P/s` throughput. A slow
lower layer therefore saturates upper-layer pools whose capacity is
concurrency, not work: the slots bind before the "real" bottleneck does. -/
theorem pool_rate_bound {inflight rate sojourn P : ℝ}
    (hlittle : inflight = rate * sojourn) (hpool : inflight ≤ P)
    (hs : 0 < sojourn) : rate ≤ P / sojourn := by
  rw [le_div_iff₀ hs]
  rw [hlittle] at hpool
  linarith

/-- Pin of the pool bound at its tight corner: any rate holding one slot
in flight at sojourn `1/4` is at most `1/(1/4)` — the instance of
`pool_rate_bound` over a free rate — and rate `4` attains the bound: it
holds one slot in flight (`1 = 4·(1/4)`) and equals `1/(1/4)`. -/
theorem pool_rate_bound_pin :
    (∀ rate : ℝ, (1 : ℝ) = rate * (1 / 4) → rate ≤ 1 / (1 / 4)) ∧
      (1 : ℝ) = 4 * (1 / 4) ∧ (4 : ℝ) = 1 / (1 / 4) :=
  ⟨fun _rate hlittle =>
      pool_rate_bound hlittle le_rfl (by norm_num),
    by norm_num, by norm_num⟩

end Overload
