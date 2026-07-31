module

public import Overload.Basic -- shake: keep
public import Overload.Capacity.Conservation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Overload.Capacity.Resources

/-!
# Example: a CPU pipeline — where the vocabulary transfers and the
metastability machinery honestly does not

A speculative out-of-order pipeline, read through this library's
vocabulary:

* **Capacity** = issue slots per cycle (here: an 8-wide machine).
* **Speculative execution = hedging**: work launched on a *predicted*
  outcome is the latency/likelihood-triggered duplicate — the
  trigger predicate is generality the scheme formalism already covers.
* **Squashed µops = the processed-duplicates waste channel**: slots spent
  on wrong-path work are capacity that produced nothing a caller kept —
  `pipelineAcct` + `pipeline_squash_caps_ipc` price it, exactly the waste
  accounting.
* **Replay/re-fetch = bounded amplification on the fetch hop**: a
  replayed µop consumes fetch/issue bandwidth again. With a replay bound
  `A`, the sustainable decode rate obeys the hop bound
  `λ ≤ C/(A·r)` (`pipeline_replay_envelope`, an instance of
  `Resources.hop_amplification_bound`).

**Honest scope, stated plainly**: a pipeline is feed-forward. No
load-coupled failure kernel is asserted (mispredict rates do not, to first
order, rise with occupancy in this stylized reading), so **no bistability
is claimed and none of the metastability machinery applies**. What
transfers is the audit vocabulary — waste accounting, amplification
envelopes, the hedging reading of speculation — and the negative claim is
itself the point: the framework says where it does *not* bind. Numbers are
stylized illustrations.
-/

@[expose] public section

namespace Overload

/-- One cycle of an 8-wide machine: 5 slots retire useful work, 2 are
squashed wrong-path µops (the processed-duplicates waste channel of
speculation-as-hedging), 1 goes idle on a stall. -/
noncomputable def pipelineAcct : Accounting where
  capacity := 8
  time := 1
  useful := 5
  wasted := 2
  idle := 1
  capacity_pos := by norm_num
  time_pos := by norm_num
  useful_nonneg := by norm_num
  wasted_nonneg := by norm_num
  idle_nonneg := by norm_num
  conserve := by norm_num

/-- Squash waste prices retirement: with a quarter of issue slots going to
wrong-path work and one slot stalled, sustained IPC is capped at
three-quarters of width less the stalled slot — 5 of 8. Disclosed: the
accounting is fully specified, so the ceiling coincides with its own
`useful` figure; the decomposition `(1-w)·C - I/T` is the transferable
part. -/
theorem pipeline_squash_caps_ipc {G : ℝ}
    (huseful : G * pipelineAcct.time * 1 ≤ pipelineAcct.useful) :
    G * 1 ≤ (1 - 1 / 4) * pipelineAcct.capacity
      - pipelineAcct.idle / pipelineAcct.time :=
  pipelineAcct.goodput_le_of_waste huseful (by unfold pipelineAcct; norm_num)

/-- **The replay envelope**: with each µop consuming one fetch slot per
attempt and a replay bound of 2 attempts, any decode rate the 8-wide fetch
hop can carry (`lam·2·1 ≤ 8`) is at most `8/(2·1) = 4` fresh µops per
cycle — the hop-amplification bound, instantiated. The fetch hop sees the
full replay amplification even though retirement only counts each µop
once. -/
theorem pipeline_replay_envelope {lam : ℝ} (hfeas : lam * 2 * 1 ≤ 8) :
    lam ≤ 8 / (2 * 1) :=
  hop_amplification_bound (K := 1) (A := 2) (r := fun _ => 1)
    (C := fun _ => 8) 0 (by norm_num) (by norm_num) hfeas

/-- Numeric regression: the boundary rate `4` meets the envelope — the
instance of `pipeline_replay_envelope` — and saturates it exactly. -/
theorem pipeline_replay_envelope_at_four :
    (4 : ℝ) ≤ 8 / (2 * 1) ∧ (4 : ℝ) = 8 / (2 * 1) :=
  ⟨pipeline_replay_envelope (by norm_num), by norm_num⟩

end Overload
