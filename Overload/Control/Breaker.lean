module

public import Overload.Basic -- shake: keep
public import Overload.Loop.ClosedLoop
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

/-!
# The circuit breaker's open state as an amplification clamp

The breaker as a mitigation: a client-side switch that, once tripped,
answers attempts locally instead of sending them to the shared resource.
This file proves the *open-state safety side only*: while open, the
amplification response is clipped at `K` attempts per request
(`breakerResponse`), a bounded loop wearing the breaker is again a bounded
loop (`BoundedLoop.breakerLoop`), and `λ·K < Θ` deletes every congested
equilibrium through the clamp theorem (`breaker_no_congestedEq`). The
same certificate re-denominated in attempts per unit time is a server-side
admission bound (`attempt_admission_no_congestedEq`).

What is deliberately **not** claimed: the breaker's dynamics. Trip/settle
thresholds, the half-open probe, flapping, and the breaker limit cycle —
the closed orbit when a breaker re-closes into a still-congested resource —
stay omitted. Nothing here says the breaker *reaches* or *stays in*
the open state; while open, the congested equilibrium does not exist.
-/

@[expose] public section

namespace Overload

/-- The open-state breaker response: the underlying amplification response
`h` clipped at the breaker's attempt allowance `K` (average attempts per
request the open breaker still lets through — health probes and the
occasional pass-through). Total for every real `K`; the intended reading has
`K ≥ 1` (the first attempt happens), but no result below needs that. -/
noncomputable def breakerResponse (h : ℝ → ℝ) (K : ℝ) : ℝ → ℝ :=
  fun p => min (h p) K

/-- The breaker never exceeds its allowance: `breakerResponse h K ≤ K` at
every failure level. The clamp leg the certificates below consume. -/
theorem breakerResponse_le (h : ℝ → ℝ) (K p : ℝ) :
    breakerResponse h K p ≤ K :=
  min_le_right _ _

namespace BoundedLoop

/-- A bounded loop wearing an open breaker: same offered rate and failure
kernel, response clipped at the allowance `K`. Only the boundedness core is
claimed — trip/settle dynamics are not modeled, so no monotone structure is
asserted or needed. -/
noncomputable def breakerLoop (L : BoundedLoop) (K : ℝ) : BoundedLoop where
  lam := L.lam
  g := L.g
  h := breakerResponse L.h K
  Amax := K
  lam_nonneg := L.lam_nonneg
  g_mem := L.g_mem
  h_le_Amax := fun p _hp => breakerResponse_le L.h K p

/-- **The open breaker is a clamp.** While the breaker is open, `λ·K < Θ`
removes every congested equilibrium of the wrapped loop — a corollary of
`clamp_no_congestedEq` with the allowance `K` as the clamp. Conditional on
the open state; whether the loop settles there is breaker dynamics, omitted. -/
theorem breaker_no_congestedEq (L : BoundedLoop) {K Θ : ℝ}
    (hK : L.lam * K < Θ) : ¬(L.breakerLoop K).CongestedEq Θ :=
  (L.breakerLoop K).clamp_no_congestedEq
    (fun p _hp => breakerResponse_le L.h K p) hK

/-- **Attempt-denominated admission is the same clamp.** A server that
accepts at most `Q` attempts per unit time is the open breaker at allowance
`K = Q/L.lam`: the clamp certificate re-denominated from attempts per
request to attempts per unit time. `Q < Θ` then removes every congested
equilibrium, with no client-side clamp, no retry budget, and no cooperation
from the caller. The clamp certificates elsewhere in the library are stated
on the demand side, which invites the reading that a caller has to
cooperate; this is the supply-side reading of the same fact.

Read against `Tightness.lean`: the completeness result quantifies over
*kernels*, not over designs. A server-side attempt bound is a different
design, not a different kernel, so it is a second sufficient mechanism
rather than a counterexample to completeness.

Mathematically new content: none. This is `breaker_no_congestedEq` at a
particular `K`. It says nothing about whether the server can enforce `Q`,
and nothing about the attempts the server rejects, which re-enter as
offered load elsewhere in the model. -/
theorem attempt_admission_no_congestedEq (L : BoundedLoop) {Q Θ : ℝ}
    (hlam : 0 < L.lam) (hQΘ : Q < Θ) :
    ¬(L.breakerLoop (Q / L.lam)).CongestedEq Θ :=
  L.breaker_no_congestedEq (by
    rw [mul_div_cancel₀ Q (ne_of_gt hlam)]
    exact hQΘ)

end BoundedLoop

/-- The demonstration loop: offered load `3`, capacity `10`, saturation
amplification `5` — inside the bistable band `[2, 10)`. -/
noncomputable abbrev breakerDemoLoop : ClosedLoop :=
  stepLoop 3 10 5 (by norm_num) (by norm_num)

/-- Non-vacuity, congested side: without the breaker the demonstration
loop sustains a congested equilibrium at capacity `10`. -/
theorem breakerDemoLoop_congestedEq : breakerDemoLoop.CongestedEq 10 :=
  stepLoop_congestedEq (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuity, breaker side: the open breaker at allowance `K = 2` deletes
that equilibrium — `λ·K = 6 < 10`. -/
theorem breakerDemoLoop_breaker_no_congestedEq :
    ¬(breakerDemoLoop.toBoundedLoop.breakerLoop 2).CongestedEq 10 :=
  breakerDemoLoop.toBoundedLoop.breaker_no_congestedEq
    (show (3 : ℝ) * 2 < 10 by norm_num)

/-- Non-vacuity, supply side: a server admitting at most `Q = 9` attempts per
unit time deletes the same equilibrium at threshold `10`, with no cooperation
from the caller. Same certificate as above, re-denominated: `Q/λ = 3`. -/
theorem breakerDemoLoop_attempt_admission_no_congestedEq :
    ¬(breakerDemoLoop.toBoundedLoop.breakerLoop (9 / 3)).CongestedEq 10 :=
  breakerDemoLoop.toBoundedLoop.attempt_admission_no_congestedEq
    (show (0 : ℝ) < 3 by norm_num) (by norm_num)

end Overload
