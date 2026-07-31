module

public import Overload.Basic -- shake: keep
public import Overload.Loop.ClosedLoop
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
# The Erlang loss law: stable recursion, closed form, and the blocking
kernel

The loss model: `c` servers, no queue, offered load `a`; an arrival
finding all servers busy is blocked. The blocking probability is Erlang's
`B(c, a)`, and practitioners compute it by the numerically stable
recursion

`B(0) = 1`,  `B(c+1) = a·B(c) / (c + 1 + a·B(c))`

because the textbook closed form `(a^c/c!) / ∑_{j≤c} a^j/j!` overflows in
floating point long before real trunk counts. This file takes the
recursion as the definition (`erlangB`) and proves:

* `erlangB_eq_closed` — **the recursion equals the closed form**: the
  identity that makes the stable computation trustworthy.
* `erlangB_mem_Icc` — blocking is a probability, for every load and
  server count.
* `erlangB_antitone_servers` — adding servers never increases blocking;
  the load-bearing step is `erlangB_carried_le`: **carried load
  `a·(1 − B)` never exceeds the server count** — no more than `c`
  servers' worth of work can be carried by `c` servers.
* `erlangB_mono_load` — more offered load never decreases blocking.
* `erlangKernel` / `erlangLoop` — the blocking probability read at
  attempt rate `Λ` over per-server rate `μ` is an admissible load-coupled
  failure kernel (in `[0,1]`, monotone), so retries against a loss system
  instantiate the loop framework via the generic truncated-geometric
  constructor, and the attempt-cap clamp certificate transfers
  (`erlangLoop_no_congestedEq`).

Modeling status, same discipline as `mm1Kernel`: the *queueing* reading —
that `B` is the stationary blocking probability of the M/M/c/c system
seen by Poisson arrivals — lives in this docstring, not in a theorem;
what is proved is the arithmetic: recursion–closed-form equality, bounds,
monotonicities, and kernel admissibility. Erlang C (queueing rather than
loss) and M/M/1/K are not attempted.
-/

@[expose] public section

namespace Overload

/-- Erlang's blocking probability for offered load `a`, by the
numerically stable recursion — the definition practitioners actually
compute. Total on all of `ℝ`; the results assume `0 ≤ a` (the denominator
is then at least `c + 1 > 0`). -/
noncomputable def erlangB (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | c + 1 => a * erlangB a c / ((c : ℝ) + 1 + a * erlangB a c)

/-- With no servers, every arrival is blocked. -/
@[simp] theorem erlangB_zero (a : ℝ) : erlangB a 0 = 1 := rfl

/-- The recursion step, as an eval lemma at the definition. -/
theorem erlangB_succ (a : ℝ) (c : ℕ) :
    erlangB a (c + 1)
      = a * erlangB a c / ((c : ℝ) + 1 + a * erlangB a c) := rfl

/-- Blocking is nonnegative. -/
theorem erlangB_nonneg {a : ℝ} (ha : 0 ≤ a) : ∀ c : ℕ, 0 ≤ erlangB a c
  | 0 => zero_le_one
  | c + 1 => by
    have hB0 := erlangB_nonneg ha c
    have hx0 : 0 ≤ a * erlangB a c := mul_nonneg ha hB0
    rw [erlangB_succ]
    exact div_nonneg hx0
      (le_of_lt (add_pos_of_pos_of_nonneg (by positivity) hx0))

/-- Blocking never exceeds one. -/
theorem erlangB_le_one {a : ℝ} (ha : 0 ≤ a) : ∀ c : ℕ, erlangB a c ≤ 1
  | 0 => le_rfl
  | c + 1 => by
    have hB0 := erlangB_nonneg ha c
    have hx0 : 0 ≤ a * erlangB a c := mul_nonneg ha hB0
    have hD : (0 : ℝ) < (c : ℝ) + 1 + a * erlangB a c :=
      add_pos_of_pos_of_nonneg (by positivity) hx0
    rw [erlangB_succ, div_le_one hD]
    linarith

/-- Blocking is a probability. -/
theorem erlangB_mem_Icc {a : ℝ} (ha : 0 ≤ a) (c : ℕ) :
    erlangB a c ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨erlangB_nonneg ha c, erlangB_le_one ha c⟩

/-- **Carried load never exceeds the server count**: `a·(1 − B(c)) ≤ c`.
The conservation fact behind server-antitonicity — `c` servers cannot
carry more than `c` servers' worth of offered work. -/
theorem erlangB_carried_le {a : ℝ} (ha : 0 ≤ a) :
    ∀ c : ℕ, a * (1 - erlangB a c) ≤ c
  | 0 => by simp
  | c + 1 => by
    have ih := erlangB_carried_le ha c
    have hB0 := erlangB_nonneg ha c
    have hD : (0 : ℝ) < (c : ℝ) + 1 + a * erlangB a c :=
      add_pos_of_pos_of_nonneg (by positivity)
        (mul_nonneg ha hB0)
    have key : a * (1 - a * erlangB a c / ((c : ℝ) + 1 + a * erlangB a c))
        = a * ((c : ℝ) + 1) / ((c : ℝ) + 1 + a * erlangB a c) := by
      field_simp
      ring
    rw [erlangB_succ, key, div_le_iff₀ hD]
    have haD : a ≤ (c : ℝ) + 1 + a * erlangB a c := by linarith
    have hc1 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
    push_cast
    linarith [mul_le_mul_of_nonneg_left haD hc1]

/-- Adding a server never increases blocking, one step. -/
theorem erlangB_succ_le {a : ℝ} (ha : 0 ≤ a) (c : ℕ) :
    erlangB a (c + 1) ≤ erlangB a c := by
  have hB0 := erlangB_nonneg ha c
  have hD : (0 : ℝ) < (c : ℝ) + 1 + a * erlangB a c :=
    add_pos_of_pos_of_nonneg (by positivity) (mul_nonneg ha hB0)
  have haD : a ≤ (c : ℝ) + 1 + a * erlangB a c := by
    have ih := erlangB_carried_le ha c
    linarith
  rw [erlangB_succ, div_le_iff₀ hD]
  linarith [mul_nonneg hB0 (sub_nonneg.mpr haD)]

/-- **Blocking is antitone in the server count.** -/
theorem erlangB_antitone_servers {a : ℝ} (ha : 0 ≤ a) :
    Antitone (erlangB a) :=
  antitone_nat_of_succ_le (erlangB_succ_le ha)

/-- **Blocking is monotone in offered load.** -/
theorem erlangB_mono_load {a a' : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a') :
    ∀ c : ℕ, erlangB a c ≤ erlangB a' c
  | 0 => le_rfl
  | c + 1 => by
    have ih := erlangB_mono_load ha haa' c
    have hB0 := erlangB_nonneg ha c
    have hx : a * erlangB a c ≤ a' * erlangB a' c :=
      mul_le_mul haa' ih hB0 (ha.trans haa')
    have hx0 : 0 ≤ a * erlangB a c := mul_nonneg ha hB0
    have h1 : (0 : ℝ) < (c : ℝ) + 1 + a * erlangB a c :=
      add_pos_of_pos_of_nonneg (by positivity) hx0
    have h2 : (0 : ℝ) < (c : ℝ) + 1 + a' * erlangB a' c :=
      add_pos_of_pos_of_nonneg (by positivity) (hx0.trans hx)
    rw [erlangB_succ, erlangB_succ, div_le_iff₀ h1, div_mul_eq_mul_div,
      le_div_iff₀ h2]
    have hc1 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
    linarith [mul_le_mul_of_nonneg_right hx hc1]

/-- The recursion multiplied against the normalizing sum telescopes to
the top term — the division-free core of the closed-form identity. -/
theorem erlangB_mul_sum {a : ℝ} (ha : 0 < a) (c : ℕ) :
    erlangB a c * (∑ j ∈ Finset.range (c + 1), a ^ j / j.factorial)
      = a ^ c / c.factorial := by
  induction c with
  | zero => norm_num [Finset.sum_range_one, Nat.factorial]
  | succ c ih =>
    have hB0 := erlangB_nonneg ha.le c
    have hD : (0 : ℝ) < (c : ℝ) + 1 + a * erlangB a c :=
      add_pos_of_pos_of_nonneg (by positivity)
        (mul_nonneg ha.le hB0)
    have hc0 : ((c.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast c.factorial_pos.ne'
    have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
    have hfact : (((c + 1).factorial : ℕ) : ℝ)
        = ((c : ℝ) + 1) * (c.factorial : ℝ) := by
      push_cast [Nat.factorial_succ]
      ring
    have hT : a ^ (c + 1) / (((c + 1).factorial : ℕ) : ℝ) * ((c : ℝ) + 1)
        = a * (a ^ c / ((c.factorial : ℕ) : ℝ)) := by
      rw [hfact, pow_succ]
      field_simp
    rw [Finset.sum_range_succ, erlangB_succ, div_mul_eq_mul_div,
      div_eq_iff hD.ne']
    linear_combination a * ih - hT

/-- **The stable recursion equals the textbook closed form** for positive
offered load (`0 < a`): `B(c, a) = (a^c/c!) / ∑_{j≤c} a^j/j!`. The
identity that makes computing by the recursion trustworthy — in machine
arithmetic the naive closed form overflows long before real server
counts, the recursion does not, and here they provably agree. -/
theorem erlangB_eq_closed {a : ℝ} (ha : 0 < a) (c : ℕ) :
    erlangB a c
      = a ^ c / c.factorial
        / ∑ j ∈ Finset.range (c + 1), a ^ j / j.factorial := by
  have hS : (0 : ℝ) < ∑ j ∈ Finset.range (c + 1), a ^ j / j.factorial :=
    Finset.sum_pos
      (fun j _ => div_pos (pow_pos ha j)
        (by exact_mod_cast j.factorial_pos))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos c)⟩
  rw [eq_div_iff hS.ne']
  exact erlangB_mul_sum ha c

/-!
## The blocking kernel: retries against a loss system

Reading the blocking probability at attempt rate `Λ` over per-server
service rate `μ` (offered load `Λ/μ`) gives a load-coupled failure
kernel satisfying both kernel hypotheses of the loop framework — the
quasi-static reading, same status as `mm1Kernel`'s.
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
  (erlangB_antitone_servers zero_le_one (Nat.zero_le 1)).trans
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
the only pin exercising the recursion past its first step. Since
`erlangB_eq_closed` matches the recursion to the closed form at every
point, this constant also certifies the closed form's value. -/
theorem erlangB_two_two : erlangB 2 2 = 2 / 5 := by
  change erlangB 2 (0 + 1 + 1) = 2 / 5
  rw [erlangB_succ, erlangB_succ]
  norm_num

end Overload
