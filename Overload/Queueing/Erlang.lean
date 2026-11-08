module

public import Overload.Basic -- shake: keep
public import Overload.Loop.ClosedLoop
public import Upstream.Analysis.SpecialFunctions.ErlangB
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

/-!
# The Erlang loss law as a blocking kernel

The loss model: `c` servers, no queue, offered load `a`. An arrival
finding all servers busy is blocked. The blocking probability is Erlang's
`B(c, a)`, `Real.erlangB a c` (`Upstream/Analysis/SpecialFunctions/ErlangB.lean`,
a copy of the parts of mathlib PR 42382 this library uses). It is defined by the numerically
stable recursion

`B(0) = 1`,  `B(c+1) = a·B(c) / (c + 1 + a·B(c))`

that practitioners compute, because the textbook closed form
`(a^c/c!) / ∑_{j≤c} a^j/j!` overflows in floating point long before real
trunk counts. That file proves that blocking is a probability
(`Real.erlangB_mem_Icc`), antitone in the server count
(`Real.erlangB_antitone`, through `Real.erlangB_carried_le`: carried load
`a·(1 − B)` never exceeds the server count) and monotone in offered load
(`Real.erlangB_mono_load`). This file reads it as a loop instance:

* `erlangKernel` / `erlangLoop` — the blocking probability read at
  attempt rate `Λ` over per-server rate `μ` is an admissible load-coupled
  failure kernel (in `[0,1]`, monotone), so retries against a loss system
  instantiate the loop framework via the generic truncated-geometric
  constructor. The attempt-cap clamp certificate transfers
  (`erlangLoop_no_congestedEq`).

Modeling status, same discipline as `mm1Kernel`: the *queueing* reading —
that `B` is the stationary blocking probability of the M/M/c/c system
seen by Poisson arrivals — lives in this docstring, not in a theorem.
What is proved is the arithmetic: bounds, monotonicities, and kernel
admissibility. Mathlib PR 42382 also proves the recursion equal to the
closed form; the copy here leaves that proof out, because nothing in this
library consumes it. Erlang C (queueing rather than
loss) and M/M/1/K are not attempted.
-/

@[expose] public section

open Real

namespace Overload

/-!
## The blocking kernel: retries against a loss system

Reading the blocking probability at attempt rate `Λ` over per-server
service rate `μ` (offered load `Λ/μ`) gives a load-coupled failure
kernel satisfying both kernel hypotheses of the loop framework. This is
the quasi-static reading, same status as `mm1Kernel`'s.
-/

/-- The Erlang blocking kernel: attempt rate → blocking probability of a
`c`-server loss system at offered load `Λ/μ`. -/
noncomputable def erlangKernel (μ : ℝ) (c : ℕ) : ℝ → ℝ :=
  fun Λ => erlangB (Λ / μ) c

/-- The blocking kernel lands in `[0, 1]`. -/
theorem erlangKernel_mem {μ : ℝ} (hμ : 0 < μ) (c : ℕ) :
    ∀ x, 0 ≤ x → erlangKernel μ c x ∈ Set.Icc (0 : ℝ) 1 :=
  fun _x hx => erlangB_mem_Icc (div_nonneg hx hμ.le) c

/-- The blocking kernel is monotone in load. -/
theorem erlangKernel_monoOn {μ : ℝ} (hμ : 0 < μ) (c : ℕ) :
    MonotoneOn (erlangKernel μ c) (Set.Ici (0 : ℝ)) := fun _x hx _y _hy hxy =>
  erlangB_mono_load (div_nonneg hx hμ.le)
    (div_le_div_of_nonneg_right hxy hμ.le) c

/-- Retries against a loss system: the truncated-geometric loop over the
Erlang blocking kernel, by the generic constructor. -/
noncomputable def erlangLoop (lam μ : ℝ) (c m : ℕ) (hlam : 0 ≤ lam)
    (hμ : 0 < μ) (hm : 1 ≤ m) : ClosedLoop :=
  kernelLoop lam (erlangKernel μ c) m hlam hm (erlangKernel_mem hμ c)
    (erlangKernel_monoOn hμ c)

/-- The attempt-cap clamp, discharged for the Erlang loop: `λ·m < Θ`
alone removes every congested equilibrium of retries against a loss
system, whatever the server count. -/
theorem erlangLoop_no_congestedEq {lam μ : ℝ} {c m : ℕ} {Θ : ℝ}
    {hlam : 0 ≤ lam} {hμ : 0 < μ} {hm : 1 ≤ m} (hK : lam * m < Θ) :
    ¬(erlangLoop lam μ c m hlam hμ hm).CongestedEq Θ :=
  (erlangLoop lam μ c m hlam hμ hm).cap_no_congestedEq
    (fun _p _hp => rfl) hK

/-- Numeric regression on monotonicity in the server count: at unit load one
server blocks no more than none does, and `erlangB_zero` says none blocks
everything. -/
theorem erlangB_antitone_servers_one : erlangB 1 1 ≤ 1 :=
  (erlangB_antitone zero_le_one (Nat.zero_le 1)).trans
    (erlangB_zero 1).le

/-- Numeric regression on the attempt-cap clamp over a loss system: at load
`1` with a cap of `2` attempts, `λ·m = 2` sits below the threshold `3`, so no
congested equilibrium survives — for the one-server, unit-rate loss kernel. -/
theorem erlangLoop_no_congestedEq_pin :
    ¬(erlangLoop 1 1 1 2 (by norm_num) (by norm_num)
      (by norm_num)).CongestedEq 3 :=
  erlangLoop_no_congestedEq (by norm_num)

/-- Numeric regression, doubling as the textbook sanity check: two servers
at offered load `2` block `2/5`. The proof unwinds `erlangB_succ` twice —
the only pin exercising the recursion past its first step. -/
theorem erlangB_two_two : erlangB 2 2 = 2 / 5 := by
  change erlangB 2 (0 + 1 + 1) = 2 / 5
  rw [erlangB_succ, erlangB_succ]
  norm_num

end Overload
