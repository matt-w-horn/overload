import Mathlib
import Overload.Coupling

/-!
# Capacity deficit as a coupled site: supply degradation in the J-matrix

The fourth sustaining mechanism (M4, supply degradation — cold caches after
restarts, GC pressure, compaction debt, connection re-establishment) as a
coupling instance, giving M4 the concrete witness the other three
mechanisms already have (SQS for re-armed timeouts, Thrashing for the
clamp, CoupledStack for spill-in coupling).

Alongside the demand deviation (site 0), track the **capacity deficit**
(site 1) as its own state. Overload erodes supply — the demand → deficit
spill `ε₂₁` — and eroded supply amplifies demand — the deficit → demand
spill `ε₁₂`. The M4 feedback loop is exactly an off-diagonal product, and
the two-site certificate machinery decides it: no spectral computation,
just the spill product against the margin product (read at sustaining
mechanism M4).

* `deficit_certified` — the stable instance: both rows contract under the
  uniform weight vector.
* `deficit_floor_blocks` — heavy erosion (`ε₂₁ = 3/2`: each unit of
  overload costs one and a half units of effective capacity) crosses the
  floor, and *no* weight vector certifies the pair — supply degradation
  sustains the overload, whatever the demand side does.

The auditable pair is (deficit → demand sensitivity, demand → deficit
erosion); reading a real system's numbers into the matrix entries is the
modeling step, as in `Coupling.lean`.
-/

namespace Overload

/-- **M4, certified stable.** Local gains `1/2` (retry response) and `3/10`
(deficit persistence), cross-couplings `2/5` (deficit inflates demand) and
`1/2` (demand erodes capacity): both rows contract under uniform weights —
`1/2 + 2/5 = 9/10 < 1` and `1/2 + 3/10 = 4/5 < 1`. -/
theorem deficit_certified : Certificate !![1/2, 2/5; 1/2, 3/10] :=
  certificate_of_two (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    one_pos one_pos (by norm_num) (by norm_num)

/-- **M4, sustaining.** With erosion `ε₂₁ = 3/2` the spill product
`2/5 · 3/2 = 3/5` crosses the margin product `(1 − 1/2)(1 − 3/10) = 7/20`:
no positive weight vector certifies the pair (`spill_floor_blocks`). The
mechanism audit's M4 leg, quantitatively: this is what "the overload is
sustained by supply degradation" looks like in the coupling algebra. -/
theorem deficit_floor_blocks : ¬Certificate !![1/2, 2/5; 3/2, 3/10] :=
  spill_floor_blocks (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Overload
