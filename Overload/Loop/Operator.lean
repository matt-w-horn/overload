module

public import Overload.Basic -- shake: keep
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.FixedPoints
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
self-map `F` of a capacity interval `[a, b]`". This file is a bespoke
Knaster–Tarski development for that situation, done directly with `sInf`/`sSup`
on `ℝ` (conditional completeness) rather than through subtype lattice
instances:

* `lfpIcc F a b` / `gfpIcc F a b` — the least/greatest fixed points, which
  bracket every fixed point in the interval. `lfpIcc` is the *healthy*
  equilibrium, `gfpIcc` the *congested* one.
* `BistableOn F a b` — the two differ. Metastability is lattice
  non-degeneracy; no crossing-counting or derivative is ever needed.
* `lfpIcc_mono_of_le` / `gfpIcc_mono_of_le` — parameter monotonicity: a
  pointwise-larger map has larger extremal fixed points, by
  prefixed/postfixed-set inclusion. The primitive the hysteresis results
  (`Hysteresis.lean`) sweep with.
* `bistableOn_of_certificate` — a **two-point certificate**: one point pushed
  down (`F x ≤ x`), one pushed up (`y ≤ F y`), `x < y`, and the order gap
  follows. Checking two inequalities replaces solving for equilibria — but
  the order gap is all it gives; `exists_two_fixedPts_of_certificate` is the
  version that carries `MonotoneOn`/`MapsTo` and concludes about equilibria.
* `iterate_le_lfpIcc` — iterates from the bottom never overshoot the healthy
  equilibrium (safe ramp-up; convergence claims would need continuity and are
  deliberately not made here).
* `lfpIcc_eq_lfp_restrict` / `gfpIcc_eq_gfp_restrict` — compatibility
  bridges: on the subtype `Set.Icc a b` (a complete lattice once `a ≤ b`),
  the bespoke construction coincides with Mathlib's `OrderHom.lfp`/`gfp` of
  the restricted map. The fixed-point theorems are read off these bridges,
  so Mathlib carries the Knaster–Tarski argument.
-/

@[expose] public section

namespace Overload

/-- Points of `[a, b]` that `F` pushes (weakly) down. -/
def prefixedPts (F : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc a b ∧ F x ≤ x}

/-- Points of `[a, b]` that `F` pushes (weakly) up. -/
def postfixedPts (F : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc a b ∧ x ≤ F x}

/-- The least fixed point of `F` on `[a, b]` (the healthy equilibrium),
realized as the infimum of the prefixed points. -/
noncomputable def lfpIcc (F : ℝ → ℝ) (a b : ℝ) : ℝ := sInf (prefixedPts F a b)

/-- The greatest fixed point of `F` on `[a, b]` (the congested equilibrium),
realized as the supremum of the postfixed points. -/
noncomputable def gfpIcc (F : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (postfixedPts F a b)

variable {F : ℝ → ℝ} {a b x y : ℝ}

/-- The prefixed points are bounded below by `a`. -/
theorem bddBelow_prefixedPts : BddBelow (prefixedPts F a b) :=
  ⟨a, fun _x hx => hx.1.1⟩

/-- The postfixed points are bounded above by `b`. -/
theorem bddAbove_postfixedPts : BddAbove (postfixedPts F a b) :=
  ⟨b, fun _x hx => hx.1.2⟩

/-- The least fixed point sits below every prefixed (in particular, every
fixed) point. No monotonicity needed. -/
theorem lfpIcc_le_of_prefixed (hx : x ∈ Set.Icc a b) (hFx : F x ≤ x) :
    lfpIcc F a b ≤ x :=
  csInf_le bddBelow_prefixedPts ⟨hx, hFx⟩

/-- The greatest fixed point sits above every postfixed (in particular, every
fixed) point. No monotonicity needed. -/
theorem le_gfpIcc_of_postfixed (hx : x ∈ Set.Icc a b) (hxF : x ≤ F x) :
    x ≤ gfpIcc F a b :=
  le_csSup bddAbove_postfixedPts ⟨hx, hxF⟩

/-- `lfpIcc` lies in `[a, b]` once `a ≤ b` and `F` maps the interval into
itself. No monotonicity needed. -/
theorem lfpIcc_mem_Icc (hab : a ≤ b)
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    lfpIcc F a b ∈ Set.Icc a b := by
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hb : b ∈ prefixedPts F a b := ⟨hb_mem, (hf hb_mem).2⟩
  exact ⟨le_csInf ⟨b, hb⟩ fun x hx => hx.1.1,
    csInf_le bddBelow_prefixedPts hb⟩

/-- `gfpIcc` lies in `[a, b]` once `a ≤ b` and `F` maps the interval into
itself. No monotonicity needed. -/
theorem gfpIcc_mem_Icc (hab : a ≤ b)
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    gfpIcc F a b ∈ Set.Icc a b := by
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have ha : a ∈ postfixedPts F a b := ⟨ha_mem, (hf ha_mem).1⟩
  exact ⟨le_csSup bddAbove_postfixedPts ha,
    csSup_le ⟨a, ha⟩ fun x hx => hx.1.2⟩

/-!
### Compatibility with Mathlib's lattice-theoretic Knaster–Tarski

Once `a ≤ b`, the subtype `Set.Icc a b` is a complete lattice
(`Set.Icc.completeLattice`), so Mathlib's `OrderHom.lfp`/`OrderHom.gfp` apply
to the restricted map. The bespoke `lfpIcc`/`gfpIcc` exist because the loop
theorems consume plain-`ℝ` statements with explicit hypotheses — the ambient
line is not a complete lattice — but nothing diverges: on the subtype, the two
constructions coincide. The fixed-point theorems `isFixedPt_lfpIcc`/
`isFixedPt_gfpIcc` below are read off these bridges, so the Knaster–Tarski
argument itself lives in Mathlib; only the `sInf`/`sSup` bookkeeping that
plain-`ℝ` statements need is proved here.
-/

/-- The restriction of `F` to `[a, b]` as an order-hom on the subtype, from
monotonicity and `MapsTo`. -/
def restrictIcc (F : ℝ → ℝ) (a b : ℝ) (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    Set.Icc a b →o Set.Icc a b where
  toFun x := ⟨F x, hf x.2⟩
  monotone' x y hxy := Subtype.mk_le_mk.mpr (hm x.2 y.2 hxy)

/-- **Bridge to Mathlib, least fixed point**: `lfpIcc` is `OrderHom.lfp` of
the restricted map, read back through the coercion. (The `Fact` instance
carries `a ≤ b`, which `Set.Icc.completeLattice` requires.) -/
theorem lfpIcc_eq_lfp_restrict [inst : Fact (a ≤ b)]
    (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    lfpIcc F a b = ↑(OrderHom.lfp (restrictIcc F a b hm hf)) := by
  have hab : a ≤ b := inst.out
  set F' := restrictIcc F a b hm hf
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hSne : {x : Set.Icc a b | F' x ≤ x}.Nonempty :=
    ⟨⟨b, hb_mem⟩, show F b ≤ b from (hf hb_mem).2⟩
  have hcoe : ((↑) '' {x : Set.Icc a b | F' x ≤ x} : Set ℝ)
      = prefixedPts F a b := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hzmem, hFz⟩
      exact ⟨⟨z, hzmem⟩, show F z ≤ z from hFz, rfl⟩
  calc lfpIcc F a b
      = sInf ((↑) '' {x : Set.Icc a b | F' x ≤ x}) := by rw [lfpIcc, hcoe]
    _ = ↑(sInf {x : Set.Icc a b | F' x ≤ x}) :=
        (Set.Icc.coe_sInf hab hSne).symm
    _ = ↑(OrderHom.lfp F') := rfl

/-- **Bridge to Mathlib, greatest fixed point**: `gfpIcc` is `OrderHom.gfp`
of the restricted map. -/
theorem gfpIcc_eq_gfp_restrict [inst : Fact (a ≤ b)]
    (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    gfpIcc F a b = ↑(OrderHom.gfp (restrictIcc F a b hm hf)) := by
  have hab : a ≤ b := inst.out
  set F' := restrictIcc F a b hm hf
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hSne : {x : Set.Icc a b | x ≤ F' x}.Nonempty :=
    ⟨⟨a, ha_mem⟩, show a ≤ F a from (hf ha_mem).1⟩
  have hcoe : ((↑) '' {x : Set.Icc a b | x ≤ F' x} : Set ℝ)
      = postfixedPts F a b := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hzmem, hzF⟩
      exact ⟨⟨z, hzmem⟩, show z ≤ F z from hzF, rfl⟩
  calc gfpIcc F a b
      = sSup ((↑) '' {x : Set.Icc a b | x ≤ F' x}) := by rw [gfpIcc, hcoe]
    _ = ↑(sSup {x : Set.Icc a b | x ≤ F' x}) :=
        (Set.Icc.coe_sSup hab hSne).symm
    _ = ↑(OrderHom.gfp F') := rfl

/-- **Knaster–Tarski, least fixed point.** A monotone self-map of `[a, b]` has
`lfpIcc` as a genuine fixed point — Mathlib's `OrderHom.isFixedPt_lfp`, read
through the compatibility bridge. -/
theorem isFixedPt_lfpIcc (hab : a ≤ b) (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    Function.IsFixedPt F (lfpIcc F a b) := by
  haveI : Fact (a ≤ b) := ⟨hab⟩
  rw [lfpIcc_eq_lfp_restrict hm hf]
  exact congrArg Subtype.val (restrictIcc F a b hm hf).isFixedPt_lfp

/-- **Knaster–Tarski, greatest fixed point.** Mathlib's
`OrderHom.isFixedPt_gfp`, read through the compatibility bridge. -/
theorem isFixedPt_gfpIcc (hab : a ≤ b) (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    Function.IsFixedPt F (gfpIcc F a b) := by
  haveI : Fact (a ≤ b) := ⟨hab⟩
  rw [gfpIcc_eq_gfp_restrict hm hf]
  exact congrArg Subtype.val (restrictIcc F a b hm hf).isFixedPt_gfp

/-- Every fixed point is bracketed by `lfpIcc` and `gfpIcc`. -/
theorem lfpIcc_le_isFixedPt (hx : x ∈ Set.Icc a b)
    (h : Function.IsFixedPt F x) : lfpIcc F a b ≤ x :=
  lfpIcc_le_of_prefixed hx h.le

/-- The upper half of the bracket: a fixed point in `[a, b]` sits below
`gfpIcc`. -/
theorem isFixedPt_le_gfpIcc (hx : x ∈ Set.Icc a b)
    (h : Function.IsFixedPt F x) : x ≤ gfpIcc F a b :=
  le_gfpIcc_of_postfixed hx h.ge

/-- For a monotone self-map of `[a, b]`, the healthy equilibrium sits below
the congested one: `lfpIcc ≤ gfpIcc`. -/
theorem lfpIcc_le_gfpIcc (hab : a ≤ b) (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    lfpIcc F a b ≤ gfpIcc F a b :=
  lfpIcc_le_isFixedPt (gfpIcc_mem_Icc hab hf) (isFixedPt_gfpIcc hab hm hf)

/-- **Parameter monotonicity, least fixed point**: a pointwise-larger map has
a larger least fixed point. Every point the larger map pushes down is pushed
down by the smaller one too — prefixed-set inclusion — so no monotonicity of
either map is needed; `G` needs `MapsTo` only to keep its prefixed set
nonempty. This is the primitive behind equilibrium sweeps: as a parameter
(offered load) rises, both extremal equilibria move up, never down. -/
theorem lfpIcc_mono_of_le {G : ℝ → ℝ} (hab : a ≤ b)
    (hFG : ∀ x ∈ Set.Icc a b, F x ≤ G x)
    (hfG : Set.MapsTo G (Set.Icc a b) (Set.Icc a b)) :
    lfpIcc F a b ≤ lfpIcc G a b := by
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hne : (prefixedPts G a b).Nonempty := ⟨b, hb_mem, (hfG hb_mem).2⟩
  refine csInf_le_csInf bddBelow_prefixedPts hne ?_
  rintro x ⟨hx, hGx⟩
  exact ⟨hx, (hFG x hx).trans hGx⟩

/-- **Parameter monotonicity, greatest fixed point**: a pointwise-larger map
has a larger greatest fixed point, by postfixed-set inclusion. Dual
asymmetry: here it is `F`, the smaller map, that needs `MapsTo` — its
postfixed set is the one that must be nonempty. -/
theorem gfpIcc_mono_of_le {G : ℝ → ℝ} (hab : a ≤ b)
    (hFG : ∀ x ∈ Set.Icc a b, F x ≤ G x)
    (hfF : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) :
    gfpIcc F a b ≤ gfpIcc G a b := by
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hne : (postfixedPts F a b).Nonempty := ⟨a, ha_mem, (hfF ha_mem).1⟩
  refine csSup_le_csSup bddAbove_postfixedPts hne ?_
  rintro x ⟨hx, hxF⟩
  exact ⟨hx, hxF.trans (hFG x hx)⟩

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

/-- A fixed point exists below every prefixed point. -/
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
  lt_of_le_of_lt (lfpIcc_le_of_prefixed hx hFx)
    (lt_of_lt_of_le hxy (le_gfpIcc_of_postfixed hy hyF))

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

/-- Ramping up from the bottom never overshoots the healthy equilibrium.
(Convergence *to* it would need continuity; deliberately not claimed.) -/
theorem iterate_le_lfpIcc (hab : a ≤ b) (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (n : ℕ) :
    F^[n] a ≤ lfpIcc F a b := by
  induction n with
  | zero => simpa using (lfpIcc_mem_Icc hab hf).1
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmem := hf.iterate n ⟨le_rfl, hab⟩
    calc F (F^[n] a) ≤ F (lfpIcc F a b) :=
          hm hmem (lfpIcc_mem_Icc hab hf) ih
      _ = lfpIcc F a b := isFixedPt_lfpIcc hab hm hf

/-- Draining from the top never undershoots the congested equilibrium —
the downward mirror of `iterate_le_lfpIcc`: iterates started at the
ceiling stay at or above `gfpIcc`. (Convergence *to* it would need
continuity; deliberately not claimed.) -/
theorem gfpIcc_le_iterate (hab : a ≤ b) (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (n : ℕ) :
    gfpIcc F a b ≤ F^[n] b := by
  induction n with
  | zero => simpa using (gfpIcc_mem_Icc hab hf).2
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmem := hf.iterate n ⟨hab, le_rfl⟩
    calc gfpIcc F a b = F (gfpIcc F a b) :=
          (isFixedPt_gfpIcc hab hm hf).symm
      _ ≤ F (F^[n] b) := hm (gfpIcc_mem_Icc hab hf) hmem ih

/-!
## Basins: the middle fixed point as the trigger-size threshold

The order-theoretic core of the separatrix and trigger-set
reframing: monotone dynamics never cross a fixed point. A burst that leaves
the state at or below the (middle) fixed point can never reach the
congested branch; a state at or past a postfixed point ratchets upward.
-/

/-- Monotone iterates never cross a fixed point from below — the basin
boundary is absorbing. This is the safe side of the trigger-size threshold:
a burst that stays at or below the middle fixed point never reaches the
congested branch. (The tipping side needs a postfixed start —
`le_iterate_of_postfixed`; monotonicity alone does not force states just
above the fixed point to ratchet up.) -/
theorem iterate_le_of_le_fixedPt {z : ℝ} (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hz : z ∈ Set.Icc a b)
    (hfz : Function.IsFixedPt F z) (hx : x ∈ Set.Icc a b) (hxz : x ≤ z)
    (n : ℕ) : F^[n] x ≤ z := by
  induction n with
  | zero => simpa using hxz
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmem := hf.iterate n hx
    have hzeq : F z = z := hfz
    calc F (F^[n] x) ≤ F z := hm hmem hz ih
      _ = z := hzeq

/-- Monotone iterates never cross a fixed point from above — the congested
side of the basin boundary, mirroring `iterate_le_of_le_fixedPt`. A drain
that starts at or above the middle fixed point never reaches the healthy
branch under monotone iteration alone; escaping downward needs a prefixed
start, not merely monotonicity. -/
theorem le_iterate_of_fixedPt_le {z : ℝ} (hm : MonotoneOn F (Set.Icc a b))
    (hf : Set.MapsTo F (Set.Icc a b) (Set.Icc a b)) (hz : z ∈ Set.Icc a b)
    (hfz : Function.IsFixedPt F z) (hx : x ∈ Set.Icc a b) (hzx : z ≤ x)
    (n : ℕ) : z ≤ F^[n] x := by
  induction n with
  | zero => simpa using hzx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hmem := hf.iterate n hx
    have hzeq : F z = z := hfz
    calc z = F z := hzeq.symm
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
