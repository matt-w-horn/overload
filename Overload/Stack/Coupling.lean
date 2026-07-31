module

public import Overload.Basic -- shake: keep
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init

/-!
# Coupled resources: weight certificates for multi-site stability

When several resources or sites exchange load (reroute, hedging, spillover),
the linearized balance is `x ↦ J·x + c` with `J` nonnegative: diagonals are
local loop gains, off-diagonals are spill sensitivities.

Instead of eigenvalue analysis, everything here runs on a **certificate**: a
nonnegative `J` together with a positive weight vector `w` satisfying
`J·w < w` componentwise (the Collatz–Wielandt witness that the spectral
radius is below one — the certificate is what the theorems consume, and it is
*checkable by evaluating `k` inequalities* plus the entry signs). The sign
condition is part of the certificate and not a side condition on the
consumers: at a *signed* `J` the weight inequalities say nothing about the
spectral radius (`!![9/10, 1; 1, -10]` contracts `w = (21, 2)` — the rows
give `20.9 < 21` and `1 < 2` — and has `ρ ≈ 10.09`), so a sign-free
certificate would not certify stability.
Classically this is the sub-invariant-weight
condition — weighted diagonal dominance, the finite-dimensional shadow of
`ρ(J) < 1` — familiar from M-matrix theory and Lyapunov-style weighted norms.
Perron–Frobenius is deliberately not used: Mathlib does not carry it, the
certificate direction (`J·w < w ⟹` stability) needs only the induction in
`certificate_decay`, and a weight vector is auditable where a spectral radius
is not.

* `two_site_certificate_iff` — for a nonnegative gain matrix over two sites
  the certificate exists **iff**
  `ε₁₂·ε₂₁ < (1-γ₁)(1-γ₂)`: individually stable sites are jointly certifiable
  exactly when the product of cross-couplings stays strictly below the
  product of stability margins. At or above it — including exact equality —
  no certificate exists (`spill_floor_blocks`).
* `certificate_fixedPoint_unique` — at most one equilibrium, by a finite
  maximum principle (no limits, no norms).
* `certificate_decay` — geometric convergence to an equilibrium in the
  `w`-weighted sense: deviations shrink by `ρ < 1` per step.
* `two_site_equilibrium_exists` — for two sites the equilibrium exists in
  closed form (the margin inequality makes the determinant positive).
* `certificate_of_small_spill` — **the headroom design rule**: any
  nonnegative sub-unit local gains tolerate all sufficiently small spill
  couplings.
* `spill_floor_blocks_weights` / `spill_floor_blocks` — **the spill floor**: a
  deterministic coupling floor at or above the margin product admits no
  contracting positive weight vector at all, and therefore blocks every
  certificate; no adaptivity restores stability without reducing the floor
  itself. The weight-level form is the stronger one: `¬Certificate` alone is
  dischargeable by the sign clause at a signed diagonal, so it is
  `spill_floor_blocks_weights` that carries the "no weights work" reading.
-/

@[expose] public section

namespace Overload

open Matrix

variable {k : ℕ} {J : Matrix (Fin k) (Fin k) ℝ}

/-- A nonnegative gain matrix together with a positive weight vector it
strictly contracts: the stability certificate for the coupled system. Both
halves are load-bearing — the weight inequalities alone are satisfiable by
signed matrices with spectral radius far above one (see the module
docstring's witness), so nonnegativity is
carried in the certificate rather than re-imposed by each consumer. -/
def Certificate (J : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ i j, 0 ≤ J i j) ∧
    ∃ w : Fin k → ℝ, (∀ i, 0 < w i) ∧ ∀ i, J.mulVec w i < w i

/-- The linearized balance iteration around an operating point. -/
def affine (J : Matrix (Fin k) (Fin k) ℝ) (c : Fin k → ℝ)
    (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => J.mulVec x i + c i

/-- Weighted-bound propagation: for entrywise-nonnegative `J` and
nonnegative envelope scale `M`, if deviations are within `M·w` and
`J·w ≤ ρ·w`, one application of `J` keeps deviations within `ρ·M·w`. -/
theorem abs_mulVec_le (hJ : ∀ i j, 0 ≤ J i j) {w : Fin k → ℝ} {ρ M : ℝ}
    (hM : 0 ≤ M) (hρw : ∀ i, J.mulVec w i ≤ ρ * w i) {x : Fin k → ℝ}
    (hx : ∀ i, |x i| ≤ M * w i) (i : Fin k) :
    |J.mulVec x i| ≤ ρ * M * w i := by
  calc |J.mulVec x i| = |∑ j, J i j * x j| := by rw [Matrix.mulVec_apply_eq_sum]
    _ ≤ ∑ j, |J i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, J i j * |x j| := Finset.sum_congr rfl fun j _ => by
        rw [abs_mul, abs_of_nonneg (hJ i j)]
    _ ≤ ∑ j, J i j * (M * w j) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hx j) (hJ i j)
    _ = M * ∑ j, J i j * w j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = M * J.mulVec w i := by rw [Matrix.mulVec_apply_eq_sum]
    _ ≤ M * (ρ * w i) := mul_le_mul_of_nonneg_left (hρw i) hM
    _ = ρ * M * w i := by ring

/-- **Geometric decay toward an equilibrium.** If an equilibrium `x⋆` of
the coupled balance exists, then for entrywise-nonnegative `J`, every
trajectory starting inside the envelope (`|x₀ − x⋆| ≤ M·w` entrywise, with
`0 ≤ M`) has deviation after `n` steps at most `ρⁿ·M·w`, for any rate
`0 ≤ ρ` with `J·w ≤ ρ·w`. Read at `ρ < 1` this is geometric decay in the
`w`-weighted sense; the statement itself asserts only the envelope. -/
theorem certificate_decay (hJ : ∀ i j, 0 ≤ J i j) {w : Fin k → ℝ}
    {ρ M : ℝ} (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ)
    (hρw : ∀ i, J.mulVec w i ≤ ρ * w i) {c xstar : Fin k → ℝ}
    (hfix : affine J c xstar = xstar) {x₀ : Fin k → ℝ}
    (h₀ : ∀ i, |x₀ i - xstar i| ≤ M * w i) (n : ℕ) (i : Fin k) :
    |((affine J c)^[n] x₀) i - xstar i| ≤ ρ ^ n * M * w i := by
  induction n generalizing i with
  | zero => simpa using h₀ i
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hstep : ∀ y : Fin k → ℝ, ∀ i,
        affine J c y i - xstar i
          = J.mulVec (fun j => y j - xstar j) i := by
      intro y i
      have hfx := congrFun hfix i
      simp only [affine] at hfx ⊢
      rw [show (fun j => y j - xstar j) = y - xstar from rfl,
        Matrix.mulVec_sub, Pi.sub_apply]
      linarith
    calc |affine J c ((affine J c)^[n] x₀) i - xstar i|
        = |J.mulVec (fun j => ((affine J c)^[n] x₀) j - xstar j) i| := by
          rw [hstep]
      _ ≤ ρ * (ρ ^ n * M) * w i :=
          abs_mulVec_le hJ (mul_nonneg (pow_nonneg hρ0 n) hM) hρw ih i
      _ = ρ ^ (n + 1) * M * w i := by ring

/-- Pin of the decay envelope on one site at gain `1/2`, three steps from a
unit deviation: the envelope reads `ρ³·M·w = 1/8`. -/
theorem certificate_decay_pin :
    |((affine !![1 / 2] ![0])^[3] ![1]) 0 - ![0] 0| ≤ (1 / 2 : ℝ) ^ 3 * 1 * 1 := by
  refine certificate_decay (J := !![1 / 2]) (w := ![1]) (ρ := 1 / 2) (M := 1)
    (c := ![0]) (xstar := ![0]) (x₀ := ![1]) ?_ zero_le_one (by norm_num) ?_ ?_
    ?_ 3 0
  · intro i j; fin_cases i; fin_cases j; norm_num
  · intro i; fin_cases i; rw [Matrix.mulVec_apply_eq_sum]; norm_num
  · funext i; fin_cases i; simp [affine, Matrix.mulVec_apply_eq_sum]
  · intro i; fin_cases i; norm_num

/-- **A certificate names a genuine contraction rate.** `Certificate` supplies
the entry signs and the strict componentwise inequalities `J·w < w`, but no
rate: the sole rate a bare certificate hands `certificate_decay` for free is
`ρ = 1`, which collapses that theorem's conclusion to the initial envelope. The weighted maximum
`ρ = maxᵢ (J·w)ᵢ / wᵢ` is a rate the same weight vector satisfies, and it is
strictly below one — finitely many strict inequalities have a strict maximum.
Feeding the pair `(w, ρ)` to `certificate_decay` gives genuine geometric decay.
The certificate's nonnegativity half is what makes the rate nonnegative. -/
theorem certificate_rate [NeZero k] (hcert : Certificate J) :
    ∃ w : Fin k → ℝ, ∃ ρ : ℝ, (∀ i, 0 < w i) ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ i, J.mulVec w i ≤ ρ * w i := by
  obtain ⟨hJ, w, hw, hJw⟩ := hcert
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := Finset.univ_nonempty
  obtain ⟨i₀⟩ : Nonempty (Fin k) := inferInstance
  refine ⟨w, Finset.univ.sup' hne (fun i => J.mulVec w i / w i), hw, ?_, ?_,
    fun i => (div_le_iff₀ (hw i)).mp
      (Finset.le_sup' (fun i => J.mulVec w i / w i) (Finset.mem_univ i))⟩
  · refine le_trans ?_
      (Finset.le_sup' (fun i => J.mulVec w i / w i) (Finset.mem_univ i₀))
    refine div_nonneg ?_ (hw i₀).le
    rw [Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hJ i₀ j) (hw j).le
  · exact (Finset.sup'_lt_iff hne).mpr fun i _ =>
      (div_lt_one (hw i)).mpr (hJw i)

/-- **Uniqueness of the coupled equilibrium**, by a finite maximum principle:
if two equilibria differed, the coordinate maximizing the weighted deviation
would strictly contract under `J`, contradicting invariance. No limits. -/
theorem certificate_fixedPoint_unique [NeZero k]
    (hcert : Certificate J) {c x y : Fin k → ℝ}
    (hx : affine J c x = x) (hy : affine J c y = y) : x = y := by
  obtain ⟨hJ, w, hw, hJw⟩ := hcert
  by_contra hne
  have heJ : ∀ i, J.mulVec (fun j => x j - y j) i = x i - y i := by
    intro i
    have hx' := congrFun hx i
    have hy' := congrFun hy i
    simp only [affine] at hx' hy'
    rw [show (fun j => x j - y j) = x - y from rfl,
      Matrix.mulVec_sub, Pi.sub_apply]
    linarith
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hne
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin k)).Nonempty)
    (fun i => |x i - y i| / w i)
  have hbound : ∀ j, |x j - y j| ≤ |x i₀ - y i₀| / w i₀ * w j := by
    intro j
    have hle : |x j - y j| / w j ≤ |x i₀ - y i₀| / w i₀ :=
      hi₀ ▸ Finset.le_sup' (fun i => |x i - y i| / w i) (Finset.mem_univ j)
    exact (div_le_iff₀ (hw j)).mp hle
  have hMpos : 0 < |x i₀ - y i₀| / w i₀ := by
    have hj : 0 < |x j₀ - y j₀| / w j₀ :=
      div_pos (abs_pos.mpr (sub_ne_zero.mpr hj₀)) (hw j₀)
    exact lt_of_lt_of_le hj
      (hi₀ ▸ Finset.le_sup' (fun i => |x i - y i| / w i)
        (Finset.mem_univ j₀))
  have hcontract : |x i₀ - y i₀| < |x i₀ - y i₀| := by
    calc |x i₀ - y i₀| = |J.mulVec (fun j => x j - y j) i₀| := by
          rw [heJ]
      _ ≤ ∑ j, |J i₀ j * (x j - y j)| := by
          rw [Matrix.mulVec_apply_eq_sum]
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, J i₀ j * |x j - y j| := Finset.sum_congr rfl fun j _ => by
          rw [abs_mul, abs_of_nonneg (hJ i₀ j)]
      _ ≤ ∑ j, J i₀ j * (|x i₀ - y i₀| / w i₀ * w j) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hbound j) (hJ i₀ j)
      _ = |x i₀ - y i₀| / w i₀ * J.mulVec w i₀ := by
          rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ < |x i₀ - y i₀| / w i₀ * w i₀ :=
          mul_lt_mul_of_pos_left (hJw i₀) hMpos
      _ = |x i₀ - y i₀| := div_mul_cancel₀ _ (ne_of_gt (hw i₀))
  exact lt_irrefl _ hcontract

/-!
## Two sites
-/

/-- Any positive weight pair strictly contracted rowwise by a **nonnegative**
2×2 gain matrix is a certificate — the `Fin 2`/`Matrix` plumbing of the
anonymous constructor, absorbed once. -/
theorem certificate_of_two {γ₁ ε₁₂ ε₂₁ γ₂ w₀ w₁ : ℝ} (hγ₁ : 0 ≤ γ₁)
    (hε₁₂ : 0 ≤ ε₁₂) (hε₂₁ : 0 ≤ ε₂₁) (hγ₂ : 0 ≤ γ₂) (h0 : 0 < w₀)
    (h1 : 0 < w₁) (hr0 : γ₁ * w₀ + ε₁₂ * w₁ < w₀)
    (hr1 : ε₂₁ * w₀ + γ₂ * w₁ < w₁) :
    Certificate !![γ₁, ε₁₂; ε₂₁, γ₂] := by
  refine ⟨?_, ![w₀, w₁], Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simpa
  · simpa using h0
  · simpa using h1
  · simpa [Matrix.mulVec_fin_two, mul_comm] using hr0
  · simpa [Matrix.mulVec_fin_two, mul_comm] using hr1

/-- **The spill floor, at the weight level**: with nonnegative spill, a
coupling product at or above the margin product `(1-γ₁)(1-γ₂)` admits *no*
contracting positive weight vector whatever. This is the sharp form of the
floor: `¬Certificate` (the corollary `spill_floor_blocks`) is dischargeable
by the certificate's sign clause alone at a signed diagonal, whereas this
statement denies the weights directly and holds at any diagonal. -/
theorem spill_floor_blocks_weights {γ₁ γ₂ ε₁₂ ε₂₁ : ℝ} (hε₁₂ : 0 ≤ ε₁₂)
    (hε₂₁ : 0 ≤ ε₂₁) (hfloor : (1 - γ₁) * (1 - γ₂) ≤ ε₁₂ * ε₂₁) :
    ¬∃ w : Fin 2 → ℝ, (∀ i, 0 < w i) ∧
      ∀ i, (!![γ₁, ε₁₂; ε₂₁, γ₂]).mulVec w i < w i := by
  rintro ⟨w, hw, hJw⟩
  have hr0 := hJw 0
  have hr1 := hJw 1
  simp only [Fin.isValue, cons_mulVec, cons_dotProduct, vecHead, vecTail, Nat.succ_eq_add_one,
    Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, dotProduct_of_isEmpty, add_zero,
    empty_mulVec, cons_val_zero, cons_val_one, cons_val_fin_one] at hr0 hr1
  have hw0 := hw 0
  have hw1 := hw 1
  have hkey : ε₁₂ * w 1 * (ε₂₁ * w 0)
      < (1 - γ₁) * w 0 * ((1 - γ₂) * w 1) :=
    mul_lt_mul'' (by linarith) (by linarith)
      (mul_nonneg hε₁₂ (le_of_lt hw1)) (mul_nonneg hε₂₁ (le_of_lt hw0))
  nlinarith [mul_pos hw0 hw1]

/-- **The two-site stability condition**: with nonnegative, sub-unit local
gains and nonnegative spill, a certificate exists **iff** the product of
cross-couplings is below the product of stability margins:
`ε₁₂ε₂₁ < (1-γ₁)(1-γ₂)`. The sign conditions are not decoration — a signed
2×2 gain matrix can satisfy the margin inequality with spectral radius far
above one (`γ₁ = γ₂ = -10`, `ε₁₂ = ε₂₁ = 10` has eigenvalues `{0, -20}`),
which is exactly what `Certificate` now excludes. -/
theorem two_site_certificate_iff {γ₁ γ₂ ε₁₂ ε₂₁ : ℝ} (hγ₁ : 0 ≤ γ₁)
    (hγ₂ : 0 ≤ γ₂) (hε₁₂ : 0 ≤ ε₁₂) (hε₂₁ : 0 ≤ ε₂₁) (h1 : γ₁ < 1)
    (h2 : γ₂ < 1) :
    Certificate !![γ₁, ε₁₂; ε₂₁, γ₂] ↔
      ε₁₂ * ε₂₁ < (1 - γ₁) * (1 - γ₂) := by
  constructor
  · rintro ⟨-, w, hw, hJw⟩
    by_contra hcon
    exact spill_floor_blocks_weights hε₁₂ hε₂₁ (not_lt.mp hcon) ⟨w, hw, hJw⟩
  · intro hlt
    rcases eq_or_lt_of_le hε₁₂ with h0 | hpos
    · -- ε₁₂ = 0: any tall-enough second weight works
      subst h0
      have hpos2 : (0 : ℝ) < 1 - γ₂ := by linarith
      have hA : 0 ≤ ε₂₁ / (1 - γ₂) := div_nonneg hε₂₁ (le_of_lt hpos2)
      refine certificate_of_two (w₀ := 1) (w₁ := ε₂₁ / (1 - γ₂) + 1)
        hγ₁ le_rfl hε₂₁ hγ₂ one_pos (by linarith) (by simpa using h1) ?_
      have hmul := (div_le_iff₀ hpos2).mp (le_refl (ε₂₁ / (1 - γ₂)))
      linarith
    · -- ε₁₂ > 0: the midpoint weight
      have hpos2 : (0 : ℝ) < 1 - γ₂ := by linarith
      have hAB : ε₂₁ / (1 - γ₂) < (1 - γ₁) / ε₁₂ :=
        (div_lt_div_iff₀ hpos2 hpos).mpr (by linarith)
      have hA : 0 ≤ ε₂₁ / (1 - γ₂) := div_nonneg hε₂₁ (le_of_lt hpos2)
      set t := (ε₂₁ / (1 - γ₂) + (1 - γ₁) / ε₁₂) / 2 with ht
      have htpos : 0 < t := by rw [ht]; linarith
      have htA : ε₂₁ / (1 - γ₂) < t := by rw [ht]; linarith
      have htB : t < (1 - γ₁) / ε₁₂ := by rw [ht]; linarith
      refine certificate_of_two hγ₁ hε₁₂ hε₂₁ hγ₂ one_pos htpos ?_ ?_
      · have := (lt_div_iff₀ hpos).mp htB
        linarith
      · have := (div_lt_iff₀ hpos2).mp htA
        linarith

/-- **Two-site equilibrium exists**: below the margin product — a positive
determinant of `I − J` — the linearized balance has a fixed point. -/
theorem two_site_equilibrium_exists {γ₁ γ₂ ε₁₂ ε₂₁ c₀ c₁ : ℝ}
    (hdet : ε₁₂ * ε₂₁ < (1 - γ₁) * (1 - γ₂)) :
    ∃ x : Fin 2 → ℝ, affine !![γ₁, ε₁₂; ε₂₁, γ₂] ![c₀, c₁] x = x := by
  have hΔpos : 0 < (1 - γ₁) * (1 - γ₂) - ε₁₂ * ε₂₁ := by linarith
  have hΔne : (1 - γ₁) * (1 - γ₂) - ε₁₂ * ε₂₁ ≠ 0 := ne_of_gt hΔpos
  set Δ := (1 - γ₁) * (1 - γ₂) - ε₁₂ * ε₂₁
  set x0 := ((1 - γ₂) * c₀ + ε₁₂ * c₁) / Δ with hx0
  set x1 := (ε₂₁ * c₀ + (1 - γ₁) * c₁) / Δ with hx1
  refine ⟨![x0, x1], funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩ <;>
    simp only [affine, Matrix.mulVec_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    rw [hx0, hx1] <;> field_simp <;> ring

/-- Pin of the two-site existence leg: local gains `1/2` with spill `1/4`
satisfy the determinant condition (`1/16 < 1/4`), so the linearized balance
has a fixed point at constant offer `(1, 1)`. -/
theorem two_site_equilibrium_exists_pin :
    ∃ x : Fin 2 → ℝ, affine !![1 / 2, 1 / 4; 1 / 4, 1 / 2] ![1, 1] x = x :=
  two_site_equilibrium_exists (by norm_num)

/-- **Diagonal dominance certifies any number of sites**: for a nonnegative
gain matrix, strictly sub-unit row sums make the uniform weight vector a
certificate — `k` additions and the entry signs to check, no eigenvalues.
Dropping the sign check would admit `!![0, 0; 0, -5]` (row sums `0 < 1`,
spectral radius `5`). -/
theorem certificate_of_row_sums {J : Matrix (Fin k) (Fin k) ℝ}
    (hJ : ∀ i j, 0 ≤ J i j) (h : ∀ i, ∑ j, J i j < 1) : Certificate J := by
  refine ⟨hJ, fun _ => 1, fun _ => one_pos, fun i => ?_⟩
  simpa [Matrix.mulVec_apply_eq_sum] using h i

/-- **The k-site headroom rule**: for a nonnegative gain matrix, diagonal
gains at most `γ < 1` and every off-diagonal spill at most `ε` with
`γ + (k-1)·ε < 1` certify the whole mesh — attenuating spill as margins
shrink always restores stability, at any number of sites. The entry-sign
hypothesis is what keeps the upper bounds from being vacuously met by large
negative gains. -/
theorem certificate_of_small_spill_pi {J : Matrix (Fin k) (Fin k) ℝ}
    {γ ε : ℝ} (hJ : ∀ i j, 0 ≤ J i j) (hdiag : ∀ i, J i i ≤ γ)
    (hoff : ∀ i j, i ≠ j → J i j ≤ ε)
    (hbound : γ + (k - 1 : ℝ) * ε < 1) : Certificate J := by
  refine certificate_of_row_sums hJ fun i => ?_
  have hsplit : ∑ j, J i j = J i i + ∑ j ∈ Finset.univ.erase i, J i j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hoffsum : ∑ j ∈ Finset.univ.erase i, J i j ≤ (k - 1 : ℝ) * ε := by
    have h := Finset.sum_le_card_nsmul (Finset.univ.erase i) (J i) ε
      fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
    rwa [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub i.pos, Nat.cast_one] at h
  rw [hsplit]
  linarith [hdiag i]

/-- **The headroom design rule**: any nonnegative sub-unit local gains
tolerate all sufficiently small spill couplings — attenuating spill as
margins shrink always restores a certificate. -/
theorem certificate_of_small_spill {γ₁ γ₂ : ℝ} (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (h1 : γ₁ < 1) (h2 : γ₂ < 1) :
    ∃ ε₀, 0 < ε₀ ∧ ∀ ε₁₂ ε₂₁, 0 ≤ ε₁₂ → 0 ≤ ε₂₁ → ε₁₂ < ε₀ → ε₂₁ < ε₀ →
      Certificate !![γ₁, ε₁₂; ε₂₁, γ₂] := by
  have hm : 0 < min (1 - γ₁) (1 - γ₂) := lt_min (by linarith) (by linarith)
  refine ⟨min (1 - γ₁) (1 - γ₂), hm,
    fun ε₁₂ ε₂₁ he1 he2 hlt1 hlt2 => ?_⟩
  rw [two_site_certificate_iff hγ₁ hγ₂ he1 he2 h1 h2]
  calc ε₁₂ * ε₂₁ < min (1 - γ₁) (1 - γ₂) * min (1 - γ₁) (1 - γ₂) :=
        mul_lt_mul'' hlt1 hlt2 he1 he2
    _ ≤ (1 - γ₁) * (1 - γ₂) :=
        mul_le_mul (min_le_left _ _) (min_le_right _ _) (le_of_lt hm)
          (by linarith)

/-- Pin of the headroom rule at local gains `1/2` and `3/4`: some positive
spill ceiling exists below which every coupling of that shape certifies. -/
theorem certificate_of_small_spill_pin :
    ∃ ε₀, 0 < ε₀ ∧ ∀ ε₁₂ ε₂₁ : ℝ, 0 ≤ ε₁₂ → 0 ≤ ε₂₁ → ε₁₂ < ε₀ → ε₂₁ < ε₀ →
      Certificate !![1 / 2, ε₁₂; ε₂₁, 3 / 4] :=
  certificate_of_small_spill (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Pin of the k-site row-sum rule at three sites: local gain `1/2` with
spill `1/8` to each of the other two leaves row sums at `3/4`, and the
uniform weight vector certifies. -/
theorem certificate_of_small_spill_pi_pin :
    Certificate !![1 / 2, 1 / 8, 1 / 8; 1 / 8, 1 / 2, 1 / 8;
      1 / 8, 1 / 8, 1 / 2] :=
  certificate_of_small_spill_pi (γ := 1 / 2) (ε := 1 / 8)
    (fun i j => by fin_cases i <;> fin_cases j <;> norm_num)
    (fun i => by fin_cases i <;> norm_num)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd rfl hij
          | norm_num)
    (by norm_num)

/-- **The spill floor**: a deterministic coupling floor at or above the
margin product blocks every certificate. Quota-driven spillover that cannot
attenuate belongs in the coupling matrix as a constant, and this is the
theorem it violates. The certificate-level corollary of
`spill_floor_blocks_weights`; for the "no weight vector works" reading cite
that one, since at a signed diagonal this conclusion also follows from the
sign clause alone. -/
theorem spill_floor_blocks {γ₁ γ₂ ε₁₂ ε₂₁ : ℝ}
    (hε₁₂ : 0 ≤ ε₁₂) (hε₂₁ : 0 ≤ ε₂₁) (h1 : γ₁ < 1) (h2 : γ₂ < 1)
    (hfloor : (1 - γ₁) * (1 - γ₂) ≤ ε₁₂ * ε₂₁) :
    ¬Certificate !![γ₁, ε₁₂; ε₂₁, γ₂] := by
  intro hcert
  have hγ₁ : 0 ≤ γ₁ := by simpa using hcert.1 0 0
  have hγ₂ : 0 ≤ γ₂ := by simpa using hcert.1 1 1
  exact absurd ((two_site_certificate_iff hγ₁ hγ₂ hε₁₂ hε₂₁ h1 h2).mp hcert)
    (not_lt.mpr hfloor)

end Overload
