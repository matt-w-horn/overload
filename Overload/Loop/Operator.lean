module

public import Overload.Basic -- shake: keep
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.FixedPoints
public import Upstream.Order.FixedPointsIcc
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

/-!
# Monotone demand operators on an interval

The closed-loop models of this library all take the form "demand is a monotone
self-map `F` of a capacity interval `[a, b]`". The extremal fixed points are
`lfpIcc F a b` and `gfpIcc F a b` (`Upstream/Order/FixedPointsIcc.lean`, a
copy of the parts of mathlib PR 42225 this library uses): the infimum of the
prefixed points and the supremum of the postfixed points of `F` in `[a, b]`,
which bracket every fixed point there once `F` is monotone on `[a, b]` and
maps it into itself (`isFixedPt_lfpIcc` with `lfpIcc_le`, `isFixedPt_gfpIcc`
with `le_gfpIcc`). `lfpIcc` is the *healthy* equilibrium, `gfpIcc` the
*congested* one. That file also carries the bracketing iterates
(`iterate_le_lfpIcc`, `gfpIcc_le_iterate`) and parameter monotonicity
(`lfpIcc_le_lfpIcc`, `gfpIcc_le_gfpIcc`), the primitive the hysteresis results
(`Hysteresis.lean`) sweep with. This file adds what the loop theorems need on
top:

* `BistableOn F a b` — the two differ. Metastability is lattice
  non-degeneracy. No crossing-counting or derivative is ever needed.
* `bistableOn_of_certificate` — a **two-point certificate**: one point pushed
  down (`F x ≤ x`), one pushed up (`y ≤ F y`), `x < y`, and the order gap
  follows. Checking two inequalities replaces solving for equilibria — but
  the order gap is all it gives. `exists_two_fixedPts_of_certificate` is the
  version that carries `MonotoneOn`/`MapsTo` and concludes about equilibria.
* The basin lemmas: monotone iterates never cross a prefixed point from below
  or a postfixed point from above.
-/

@[expose] public section

namespace Overload

variable {F : ℝ → ℝ} {a b x y : ℝ}

/-- A prefixed point truncates the interval from above invariantly. -/
theorem mapsTo_Icc_of_prefixed (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hx : x ∈ Set.Icc a b)
    (hFx : F x ≤ x) : Set.MapsTo F (Set.Icc a x) (Set.Icc a x) := by
  intro z hz
  have hz' : z ∈ Set.Icc a b := ⟨hz.1, le_trans hz.2 hx.2⟩
  exact ⟨(hf hz').1, le_trans (hm hz' hx hz.2) hFx⟩

/-- A postfixed point truncates the interval from below invariantly. -/
theorem mapsTo_Icc_of_postfixed (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hy : y ∈ Set.Icc a b)
    (hyF : y ≤ F y) : Set.MapsTo F (Set.Icc y b) (Set.Icc y b) := by
  intro z hz
  have hz' : z ∈ Set.Icc a b := ⟨le_trans hy.1 hz.1, hz.2⟩
  exact ⟨le_trans hyF (hm hy hz' hz.1), (hf hz').2⟩

/-- For a monotone self-map of `[a, b]`, a fixed point exists in `[a, x]`
for every prefixed point `x ∈ [a, b]`: at or below the prefixed point,
without leaving the interval. -/
theorem exists_fixedPt_le (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hx : x ∈ Set.Icc a b)
    (hFx : F x ≤ x) : ∃ z ∈ Set.Icc a x, Function.IsFixedPt F z := by
  have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hx.2
  have hm' : MonotoneOn F (Set.Icc a x) := hm.mono hsub
  have hf' := mapsTo_Icc_of_prefixed hm hf hx hFx
  exact ⟨lfpIcc F a x, lfpIcc_mem_Icc hx.1 hf', isFixedPt_lfpIcc hx.1 hm' hf'⟩

/-- A fixed point exists above every postfixed point. -/
theorem exists_fixedPt_ge (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hy : y ∈ Set.Icc a b)
    (hyF : y ≤ F y) : ∃ z ∈ Set.Icc y b, Function.IsFixedPt F z := by
  have hsub : Set.Icc y b ⊆ Set.Icc a b := Set.Icc_subset_Icc_left hy.1
  have hm' : MonotoneOn F (Set.Icc y b) := hm.mono hsub
  have hf' := mapsTo_Icc_of_postfixed hm hf hy hyF
  exact ⟨gfpIcc F y b, gfpIcc_mem_Icc hy.2 hf', isFixedPt_gfpIcc hy.2 hm' hf'⟩

/-- Bistability as an order gap: `lfpIcc < gfpIcc`. Read it together with the
side conditions: for a *monotone self-map* of `[a, b]` the two values are
genuine fixed points (`isFixedPt_lfpIcc`/`isFixedPt_gfpIcc`), and
`exists_two_fixedPts_of_certificate` upgrades a certificate to two separated
equilibria. Without monotonicity and `MapsTo`, `lfpIcc`/`gfpIcc` are infima
and suprema of possibly-empty sets (junk values), and `BistableOn` alone
asserts nothing about fixed points. -/
def BistableOn (F : ℝ → ℝ) (a b : ℝ) : Prop := lfpIcc F a b < gfpIcc F a b

/-- **Two-point bistability certificate.** One point pushed down, a strictly
larger point pushed up — two inequality checks — force the order gap
`lfpIcc < gfpIcc`. No equation solving, no derivative, no crossing count.

Read it as `BistableOn` is defined: an order gap, and nothing more. This
statement takes neither `MonotoneOn` nor `MapsTo`, so `lfpIcc`/`gfpIcc` need
not be fixed points at all — `F x = if x < 2 then -1 else 5` satisfies the
certificate on `[0, 4]` with no fixed point there. For the two-equilibria
reading use `exists_two_fixedPts_of_certificate`, which carries the two side
conditions and concludes about genuine fixed points. -/
theorem bistableOn_of_certificate (hx : x ∈ Set.Icc a b) (hFx : F x ≤ x)
    (hy : y ∈ Set.Icc a b) (hyF : y ≤ F y) (hxy : x < y) :
    BistableOn F a b :=
  lt_of_le_of_lt (lfpIcc_le hx hFx) (lt_of_lt_of_le hxy (le_gfpIcc hy hyF))

/-- The certificate upgraded to two genuine, separated fixed points. -/
theorem exists_two_fixedPts_of_certificate (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hx : x ∈ Set.Icc a b)
    (hFx : F x ≤ x) (hy : y ∈ Set.Icc a b) (hyF : y ≤ F y) (hxy : x < y) :
    ∃ z₁ z₂, Function.IsFixedPt F z₁ ∧ Function.IsFixedPt F z₂ ∧
      z₁ ≤ x ∧ y ≤ z₂ ∧ z₁ < z₂ := by
  obtain ⟨z₁, hz₁mem, hz₁⟩ := exists_fixedPt_le hm hf hx hFx
  obtain ⟨z₂, hz₂mem, hz₂⟩ := exists_fixedPt_ge hm hf hy hyF
  exact ⟨z₁, z₂, hz₁, hz₂, hz₁mem.2,
    hz₂mem.1, lt_of_le_of_lt hz₁mem.2 (lt_of_lt_of_le hxy hz₂mem.1)⟩

/-!
## Basins: the middle fixed point as the trigger-size threshold

The order-theoretic core of the separatrix and trigger-set
reframing: monotone dynamics never cross a fixed point. A burst that leaves
the state at or below the (middle) fixed point can never reach the
congested branch. A state at or past a postfixed point ratchets upward.
-/

/-- Monotone iterates never cross a prefixed point from below — the basin
boundary is absorbing. This is the safe side of the trigger-size threshold:
a burst that stays at or below a prefixed point `F z ≤ z` (in particular, any
fixed point `F z = z`) never crosses `z`. (The tipping side needs a postfixed
start — `le_iterate_of_postfixed`; monotonicity alone does not force states
just above a fixed point to ratchet up.) -/
theorem iterate_le_of_le_fixedPt {z : ℝ} (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hz : z ∈ Set.Icc a b)
    (hfz : F z ≤ z) (hx : x ∈ Set.Icc a b) (hxz : x ≤ z)
    (n : ℕ) : F^[n] x ≤ z := by
  induction n with
  | zero => simpa using hxz
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmem := hf.iterate n hx
    calc F (F^[n] x) ≤ F z := hm hmem hz ih
      _ ≤ z := hfz

/-- Monotone iterates never cross a postfixed point from above — the congested
side of the basin boundary, mirroring `iterate_le_of_le_fixedPt`. With `F`
monotone on `[a, b]` and mapping `[a, b]` into itself, a drain that starts in
`[a, b]` at or above a postfixed point `z ∈ [a, b]` with `z ≤ F z` (in
particular, any fixed point `F z = z`) never crosses below `z`; escaping
downward needs a prefixed start. -/
theorem le_iterate_of_fixedPt_le {z : ℝ} (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hz : z ∈ Set.Icc a b)
    (hfz : z ≤ F z) (hx : x ∈ Set.Icc a b) (hzx : z ≤ x)
    (n : ℕ) : z ≤ F^[n] x := by
  induction n with
  | zero => simpa using hzx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmem := hf.iterate n hx
    calc z ≤ F z := hfz
      _ ≤ F (F^[n] x) := hm hz hmem ih

/-- From a postfixed state, monotone iterates ratchet upward — the formal
shard of "past the separatrix, the storm feeds itself". -/
theorem le_iterate_of_postfixed (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hy : y ∈ Set.Icc a b)
    (hyF : y ≤ F y) (n : ℕ) : F^[n] y ≤ F^[n + 1] y := by
  induction n with
  | zero => simpa using hyF
  | succ n ih =>
    have h1 := hm (hf.iterate n hy) (hf.iterate (n + 1) hy) ih
    rwa [← Function.iterate_succ_apply' F n,
      ← Function.iterate_succ_apply' F (n + 1)] at h1

end Overload
