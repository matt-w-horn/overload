import Mathlib

/-!
# Work conservation at the bottleneck

The accounting frame: over an observation window, capacity·time splits
exactly into useful, wasted, and idle work — no mechanism manufactures
capacity. The scheme-agnostic goodput bound `G ≤ min(λ, C/s̄)` follows from
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
  capacity_pos : 0 < capacity
  time_pos : 0 < time
  useful_nonneg : 0 ≤ useful
  wasted_nonneg : 0 ≤ wasted
  idle_nonneg : 0 ≤ idle
  /-- Conservation: the bottleneck neither manufactures nor destroys capacity. -/
  conserve : useful + wasted + idle = capacity * time

namespace Accounting

variable (A : Accounting)

theorem useful_le : A.useful ≤ A.capacity * A.time := by
  linarith [A.conserve, A.wasted_nonneg, A.idle_nonneg]

/-- **The scheme-agnostic goodput bound** `G ≤ min(λ, C/s̄)`: goodput `G` is
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
capacity·time is wasted, then `G·s̄ ≤ (1-w)·C - I/T`. Both subtractions are
sharp — the conclusion is the useful-work hypothesis re-expressed through
conservation, with `wasted` and `idle` named instead of `useful`. That is
the whole content: the waste fraction relabels the ceiling, it does not
tighten it, so a statement dropping the idle term (`G·s̄ ≤ (1-w)·C`) would
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

/-- Pin of the pool bound at its tight corner: one slot held for a quarter of
a second admits `4` requests per second, and the bound is attained there. -/
theorem pool_rate_bound_pin : (4 : ℝ) ≤ 1 / (1 / 4) :=
  pool_rate_bound (inflight := 1) (by norm_num) (by norm_num) (by norm_num)

end Overload
