module

public import Overload.Basic -- shake: keep
public import Overload.Stack.Coupling
public import Overload.Loop.Signature
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
import Mathlib.Topology.Sheaves.Init

/-!
# The fan-in star: assume-guarantee contracts over a shared sink

The fan-in shape: servers `i = 1..k`, each with fresh load `λᵢ`,
amplification response `hᵢ`, and fan-out ratio `rᵢ` into one shared
downstream sink whose failure kernel is `g_D`. Demand balance is the
coupled system `Λᵢ = λᵢ·hᵢ(g_D(∑ⱼ rⱼΛⱼ))`.

The organizing observation is a worst-case, order-theoretic form of the
flow-equivalent server: the sink's aggregate `y = ∑ rⱼΛⱼ` satisfies the
*scalar* fixed-point equation `y = ∑ rᵢλᵢhᵢ(g_D y)`, so the whole star
collapses to one closed loop (`Star.toLoop`) — exactly, for the safety
question (`Star.congestedEq_iff`) — and any scalar equilibrium unpacks
back into a genuine componentwise vector equilibrium
(`Star.isVectorEq`).

The assume-guarantee reading:

* `Star.Contract` — what a team certifies about its own server, with no
  knowledge of the others: a clamp `hᵢ ≤ Kᵢ`.
* `Star.signature` — the one number a team exports: `σᵢ = λᵢKᵢrᵢ`.
* `Star.no_congestedEq_of_signatures` — **the star clamp: contracts
  compose by addition.** `∑ σᵢ < Θ` removes every congested equilibrium
  at the sink, for any sink kernel — each team checks only its own row,
  and fan-in aggregation is a sum (as within-server aggregation is a
  `min`, `Resources.lean`'s `binding_shift`, and down-stack aggregation is
  a product, `capProd`).
* `starWitness` — a heterogeneous two-server star over the saturated
  sink kernel with both equilibria exact (`8` and `24`): bistable
  fan-in, and the sibling at lighter loads certified by the signature
  sum alone.
* `star_signature_not_decide_congestedEq` — the matching impossibility:
  no certificate reading only the exported sum decides congestion at the
  sink, witnessed at one server and unit fan-out through the embedding
  `ClosedLoop.toStar`.

The gain side, eigenvalue-free as in `Coupling.lean`:

* `rankOne_certificate_iff` — for `J = a·bᵀ` with nonnegative factors, a
  positive sub-invariant weight (`Certificate`) exists **iff** the
  pairing sum `∑ bⱼaⱼ < 1` — the certificate form of "a rank-one
  nonnegative matrix's sole nonzero eigenvalue is `⟨b, a⟩`", with the
  weight `w = a + ε` explicit and the converse by pairing with `b`.
* `Star.gainMatrix_certificate_iff` — the star's linearized coupling
  matrix is exactly rank-one (`Jᵢⱼ = (λᵢLᵢℓ_D)·rⱼ`), so local stability
  has a scalar criterion: a certificate exists iff the star gain
  `∑ rᵢλᵢLᵢℓ_D < 1`. Through `Coupling`, the certificate delivers
  geometric decay (`certificate_decay`) and equilibrium uniqueness
  (`certificate_fixedPoint_unique`, consumed here as
  `Star.gain_unique_eq`).

Honest boundaries, stated: the entries `Lᵢ`, `ℓ_D` of the gain matrix
are Lipschitz surrogates for the derivative products `λᵢhᵢ'g_D'` —
modeling inputs, the same status as the mesh example's coupling entries;
the signature `σᵢ` forgets the shape of `hᵢ`, so a contract certifies
*absence* of congestion, one direction, and no certificate reading only
the exported sum decides congestion at the sink
(`star_signature_not_decide_congestedEq`);
and the reduction is clamp-side — the order-theoretic existence results
would need a monotone aggregate with an amplification floor, which the
star does not assume.
-/

@[expose] public section

namespace Overload

open Matrix

/-- A fan-in star: `k` servers feeding one shared sink. Server `i` offers
fresh load `lam i`, amplifies by `h i`, and forwards a fraction `r i` of
its demand to the sink, whose load-coupled failure kernel is `gD`. -/
structure Star (k : ℕ) where
  /-- Fresh offered load at server `i`. -/
  lam : Fin k → ℝ
  /-- Fan-out ratio: the fraction of server `i`'s demand that lands on
  the shared sink. -/
  r : Fin k → ℝ
  /-- Per-server amplification response: sink failure probability →
  expected attempts per request at server `i`. -/
  h : Fin k → ℝ → ℝ
  /-- The sink's load-coupled failure kernel. -/
  gD : ℝ → ℝ
  /-- Loads are nonnegative. -/
  lam_nonneg : ∀ i, 0 ≤ lam i
  /-- Fan-out ratios are nonnegative. -/
  r_nonneg : ∀ i, 0 ≤ r i
  /-- The sink kernel is a probability. -/
  gD_mem : ∀ x, 0 ≤ x → gD x ∈ Set.Icc (0 : ℝ) 1

namespace Star

variable {k : ℕ} (S : Star k)

/-- The aggregate response: what the sink receives per failure level —
the flow-equivalent server's response curve. -/
def aggResponse (p : ℝ) : ℝ := ∑ i, S.r i * S.lam i * S.h i p

/-- The sink's scalar demand operator: the star collapsed to one loop.
A fixed point is a self-consistent aggregate attempt rate at the sink. -/
def F (y : ℝ) : ℝ := S.aggResponse (S.gD y)

/-- A congested equilibrium at the sink at threshold `Θ`: a
self-sustaining aggregate at or above `Θ`. `Star.isVectorEq` upgrades
the scalar witness to a componentwise vector equilibrium. -/
def CongestedEq (Θ : ℝ) : Prop := ∃ y, 0 ≤ y ∧ S.F y = y ∧ Θ ≤ y

/-- **Scalar equilibria are vector equilibria.** From a fixed point of
the collapsed operator, per-server demands `Λᵢ = λᵢhᵢ(g_D y)` satisfy
the componentwise balance equations, and the sink sees exactly their
weighted sum — the flow-equivalent reduction loses nothing. -/
theorem isVectorEq {y : ℝ} (hfix : S.F y = y) :
    ∃ Λ : Fin k → ℝ, (∑ j, S.r j * Λ j) = y ∧
      ∀ i, Λ i = S.lam i * S.h i (S.gD (∑ j, S.r j * Λ j)) := by
  have hsum : (∑ j, S.r j * (S.lam j * S.h j (S.gD y))) = y :=
    (Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm).trans hfix
  refine ⟨fun i => S.lam i * S.h i (S.gD y), hsum, fun i => ?_⟩
  change S.lam i * S.h i (S.gD y)
      = S.lam i * S.h i (S.gD (∑ j, S.r j * (S.lam j * S.h j (S.gD y))))
  rw [hsum]

/-- What a team certifies about its own server, with no knowledge of the
others: a clamp on its amplification response. -/
def Contract (K : Fin k → ℝ) : Prop :=
  ∀ i, ∀ p ∈ Set.Icc (0 : ℝ) 1, S.h i p ≤ K i

/-- The per-server signature: the one number a team exports under its
contract — load times clamp times fan-out, `σᵢ = λᵢKᵢrᵢ`. -/
def signature (K : Fin k → ℝ) (i : Fin k) : ℝ := S.lam i * K i * S.r i

/-- Under contracts, the aggregate response is bounded by the signature
sum — the only fact about the servers the sink ever needs. -/
theorem aggResponse_le {K : Fin k → ℝ} (hK : S.Contract K) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1, S.aggResponse p ≤ ∑ i, S.signature K i := by
  intro p hp
  apply Finset.sum_le_sum
  intro i _
  calc S.r i * S.lam i * S.h i p
      ≤ S.r i * S.lam i * K i :=
        mul_le_mul_of_nonneg_left (hK i p hp)
          (mul_nonneg (S.r_nonneg i) (S.lam_nonneg i))
    _ = S.signature K i := by
        change _ = S.lam i * K i * S.r i
        ring

/-- **The flow-equivalent server**: the star collapsed to a single
scalar `BoundedLoop` at unit offered rate with the aggregate response.
The reduction is exact for the safety question
(`Star.congestedEq_iff`). -/
def toLoop (A : ℝ)
    (hA : ∀ p ∈ Set.Icc (0 : ℝ) 1, S.aggResponse p ≤ A) : BoundedLoop where
  lam := 1
  g := S.gD
  h := S.aggResponse
  Amax := A
  lam_nonneg := zero_le_one
  g_mem := S.gD_mem
  h_le_Amax := hA

variable {S} in
/-- The star and its flow-equivalent server have the same congested
equilibria at the sink. -/
theorem congestedEq_iff {A Θ : ℝ}
    (hA : ∀ p ∈ Set.Icc (0 : ℝ) 1, S.aggResponse p ≤ A) :
    (S.toLoop A hA).CongestedEq Θ ↔ S.CongestedEq Θ := by
  have hF : ∀ y, (S.toLoop A hA).F y = S.F y := fun y => one_mul _
  unfold BoundedLoop.CongestedEq CongestedEq
  exact exists_congr fun y => by rw [hF]

/-- **The star clamp: local contracts compose by addition.** If each
team certifies only its own clamp `hᵢ ≤ Kᵢ` and the signatures sum below
the sink threshold — `∑ λᵢKᵢrᵢ < Θ` — no congested equilibrium exists at
the sink, for any sink kernel. Fan-in aggregation of certificates is a
sum, with no team needing to know another's internals. -/
theorem no_congestedEq_of_signatures {K : Fin k → ℝ} {Θ : ℝ}
    (hK : S.Contract K) (hsig : ∑ i, S.signature K i < Θ) :
    ¬S.CongestedEq Θ := by
  intro hcong
  refine (S.toLoop (∑ i, S.signature K i)
      (S.aggResponse_le hK)).clamp_no_congestedEq (S.aggResponse_le hK)
    ?_ ((congestedEq_iff (S.aggResponse_le hK)).mpr hcong)
  change (1 : ℝ) * (∑ i, S.signature K i) < Θ
  linarith

end Star

/-!
## The rank-one gain certificate

The star's linearized coupling matrix is `Jᵢⱼ = aᵢ·bⱼ` with
`aᵢ = λᵢLᵢℓ_D` (per-server response slope surrogate into the sink) and
`bⱼ = rⱼ` (fan-in weights). For rank-one nonnegative matrices the
`Coupling.lean` weight certificate has a *scalar* criterion.
-/

/-- Forward direction: if the pairing sum is below one, the explicit
weight `w = a + ε` certifies `J = a·bᵀ`. -/
theorem rankOne_certificate_of_pairing_lt {k : ℕ} {a b : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hs : ∑ j, b j * a j < 1) :
    Certificate (Matrix.of fun i j => a i * b j) := by
  refine ⟨fun i j => mul_nonneg (ha i) (hb j), ?_⟩
  have hB0 : 0 ≤ ∑ j, b j := Finset.sum_nonneg fun j _ => hb j
  rcases eq_or_lt_of_le hB0 with hB | hB
  · -- degenerate fan-in: all weights zero, any positive vector works
    have hb0 : ∀ j ∈ Finset.univ, b j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hb j).mp hB.symm
    refine ⟨fun _ => 1, fun _ => one_pos, fun i => ?_⟩
    rw [mulVec_apply']
    have hz : ∑ j, (Matrix.of fun i j => a i * b j) i j * 1 = 0 :=
      Finset.sum_eq_zero fun j hj => by
        change a i * b j * 1 = 0
        rw [hb0 j hj]
        ring
    rw [hz]
    norm_num
  · set s := ∑ j, b j * a j with hs_def
    set B := ∑ j, b j with hB_def
    set ε := (1 - s) / (2 * B) with hε_def
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    refine ⟨fun i => a i + ε, fun i => by have := ha i; linarith,
      fun i => ?_⟩
    rw [mulVec_apply']
    have hexpand : ∑ j, (Matrix.of fun i j => a i * b j) i j * (a j + ε)
        = a i * s + a i * ε * B := by
      rw [hs_def, hB_def, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        change a i * b j * (a j + ε) = _
        ring
    rw [hexpand]
    have hεB : ε * B = (1 - s) / 2 := by
      rw [hε_def]
      field_simp
    nlinarith [mul_nonneg (ha i) (by linarith : (0 : ℝ) ≤ 1 - s)]

/-- Converse, by pairing with the fan-in weights: any certificate forces
the pairing sum below one. -/
theorem pairing_lt_of_rankOne_certificate {k : ℕ} {a b : Fin k → ℝ}
    (hb : ∀ j, 0 ≤ b j)
    (hcert : Certificate (Matrix.of fun i j => a i * b j)) :
    ∑ j, b j * a j < 1 := by
  obtain ⟨-, w, hw, hJw⟩ := hcert
  by_cases hbz : ∀ j, b j = 0
  · have hz : ∑ j, b j * a j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hbz j, zero_mul]
    rw [hz]
    norm_num
  · push Not at hbz
    obtain ⟨j₀, hj₀⟩ := hbz
    have hbj₀ : 0 < b j₀ := (hb j₀).lt_of_ne (Ne.symm hj₀)
    have hpair : ∑ i, b i * (Matrix.of fun i j => a i * b j).mulVec w i
        < ∑ i, b i * w i := by
      apply Finset.sum_lt_sum
      · exact fun i _ => mul_le_mul_of_nonneg_left (hJw i).le (hb i)
      · exact ⟨j₀, Finset.mem_univ j₀,
          mul_lt_mul_of_pos_left (hJw j₀) hbj₀⟩
    have hLHS : ∑ i, b i * (Matrix.of fun i j => a i * b j).mulVec w i
        = (∑ j, b j * a j) * (∑ j, b j * w j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mulVec_apply', Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change b i * ((a i * b j) * w j) = b i * a i * (b j * w j)
      ring
    have hbw : 0 < ∑ j, b j * w j := by
      apply Finset.sum_pos'
      · exact fun j _ => mul_nonneg (hb j) (hw j).le
      · exact ⟨j₀, Finset.mem_univ j₀, mul_pos hbj₀ (hw j₀)⟩
    rw [hLHS] at hpair
    exact (mul_lt_iff_lt_one_left hbw).mp hpair

/-- **The rank-one certificate criterion**: for `J = a·bᵀ` with
nonnegative factors, a positive sub-invariant weight exists **iff** the
pairing sum is below one — the eigenvalue-free form of "the sole nonzero
eigenvalue of a nonnegative rank-one matrix is `⟨b, a⟩`". -/
theorem rankOne_certificate_iff {k : ℕ} {a b : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    Certificate (Matrix.of fun i j => a i * b j)
      ↔ ∑ j, b j * a j < 1 :=
  ⟨pairing_lt_of_rankOne_certificate hb,
    rankOne_certificate_of_pairing_lt ha hb⟩

namespace Star

variable {k : ℕ} (S : Star k)

/-- The star's linearized coupling matrix at response-slope surrogates:
`Jᵢⱼ = (λᵢLᵢℓ_D)·rⱼ` — server `j`'s demand feeds the sink by `rⱼ`, and
the sink's failure level moves server `i`'s demand by `λᵢLᵢℓ_D`. The
entries `Lᵢ` (per-server response slope) and `ℓ_D` (sink kernel slope)
are Lipschitz surrogates for `hᵢ'` and `g_D'` — **modeling inputs**,
the same status as the mesh example's coupling entries. -/
def gainMatrix (L : Fin k → ℝ) (ℓD : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => S.lam i * L i * ℓD * S.r j

/-- The star gain: the scalar the fan-in structure reduces stability to,
`∑ rⱼ·λⱼLⱼℓ_D`. -/
def gain (L : Fin k → ℝ) (ℓD : ℝ) : ℝ :=
  ∑ j, S.r j * (S.lam j * L j * ℓD)

variable {S} in
/-- **The star gain criterion**: the linearized star admits a weight
certificate **iff** its scalar gain is below one — the flow-equivalent
server's stability condition, with no eigenvalue computed. -/
theorem gainMatrix_certificate_iff {L : Fin k → ℝ} {ℓD : ℝ}
    (hL : ∀ i, 0 ≤ L i) (hℓD : 0 ≤ ℓD) :
    Certificate (S.gainMatrix L ℓD) ↔ S.gain L ℓD < 1 :=
  rankOne_certificate_iff
    (fun i => mul_nonneg (mul_nonneg (S.lam_nonneg i) (hL i)) hℓD)
    S.r_nonneg

/-- Below unit gain the star's linearized equilibrium is unique — the
finite maximum principle, consumed through the rank-one
criterion. -/
theorem gain_unique_eq [NeZero k] {L : Fin k → ℝ} {ℓD : ℝ}
    (hL : ∀ i, 0 ≤ L i) (hℓD : 0 ≤ ℓD) (hgain : S.gain L ℓD < 1)
    {c x y : Fin k → ℝ} (hx : affine (S.gainMatrix L ℓD) c x = x)
    (hy : affine (S.gainMatrix L ℓD) c y = y) : x = y :=
  certificate_fixedPoint_unique
    ((gainMatrix_certificate_iff hL hℓD).mpr hgain) hx hy

end Star

/-!
## The two-server witness

Heterogeneous servers — a doubling retrier and a 4× retrier — at loads
`4` each, unit fan-out, over a saturated sink of capacity `10`. Both
equilibria are exact points, no fixed-point machinery needed: healthy at
`8 = 4+4` (fresh loads alone), congested at `24 = 8+16` (both fully
amplified). The lighter sibling at unit loads is certified by the
signature sum `2 + 4 = 6 < 10` — the star clamp applied to numbers.
-/

/-- The two-server star witness over the saturated sink kernel. -/
noncomputable abbrev starWitness : Star 2 where
  lam := ![4, 4]
  r := ![1, 1]
  h := ![fun p => 1 + p, fun p => 1 + 3 * p]
  gD := stepKernel 10
  lam_nonneg := by rw [Fin.forall_fin_two]; constructor <;> norm_num
  r_nonneg := by rw [Fin.forall_fin_two]; constructor <;> norm_num
  gD_mem := stepKernel_mem 10

/-- The witness's demand operator in closed form: fresh loads plus the
kernel-scaled amplification headroom. -/
theorem starWitness_F (y : ℝ) :
    starWitness.F y = 8 + 16 * stepKernel 10 y := by
  change (∑ i : Fin 2, starWitness.r i * starWitness.lam i
      * starWitness.h i (stepKernel 10 y)) = 8 + 16 * stepKernel 10 y
  rw [Fin.sum_univ_two]
  change (1 : ℝ) * 4 * (1 + stepKernel 10 y)
      + 1 * 4 * (1 + 3 * stepKernel 10 y) = 8 + 16 * stepKernel 10 y
  ring

/-- **A bistable fan-in star**: the healthy aggregate `8` and the
congested aggregate `24` are both exact fixed points — heterogeneous
servers, one shared sink, two coexisting sink states. -/
theorem starWitness_bistable : BistableOn starWitness.F 0 24 := by
  refine bistableOn_of_certificate (x := 8) (y := 24)
    ⟨by norm_num, by norm_num⟩ ?_ ⟨by norm_num, by norm_num⟩ ?_
    (by norm_num)
  · rw [starWitness_F, stepKernel_of_lt (by norm_num)]
    norm_num
  · rw [starWitness_F, stepKernel_of_ge (by norm_num)]
    norm_num

/-- The congested state is a genuine sink equilibrium at capacity. -/
theorem starWitness_congestedEq : starWitness.CongestedEq 10 :=
  ⟨24, by norm_num,
    by rw [starWitness_F, stepKernel_of_ge (by norm_num)]; norm_num,
    by norm_num⟩

/-- Numeric regression on the vector unpacking: the witness's congested
aggregate `24` comes back as per-server demands whose fan-out-weighted sum is
again `24`, each solving its own balance equation. -/
theorem starWitness_isVectorEq :
    ∃ Λ : Fin 2 → ℝ, (∑ j, starWitness.r j * Λ j) = 24 ∧
      ∀ i, Λ i = starWitness.lam i *
        starWitness.h i (starWitness.gD (∑ j, starWitness.r j * Λ j)) :=
  starWitness.isVectorEq
    (by rw [starWitness_F, stepKernel_of_ge (by norm_num)]; norm_num)

/-- The same mechanisms at unit fresh loads: the clamped sibling. -/
noncomputable abbrev starWitnessLight : Star 2 :=
  { starWitness with
    lam := ![1, 1]
    lam_nonneg := by rw [Fin.forall_fin_two]; constructor <;> norm_num }

/-- **The star clamp on numbers**: signatures `1·2·1 + 1·4·1 = 6 < 10`,
so the sink is certified — each team checked only its own clamp. -/
theorem starWitnessLight_no_congestedEq :
    ¬starWitnessLight.CongestedEq 10 := by
  refine starWitnessLight.no_congestedEq_of_signatures
    (K := ![2, 4]) ?_ ?_
  · exact Fin.forall_fin_two.mpr
      ⟨fun p hp => by change 1 + p ≤ 2; linarith [hp.2],
        fun p hp => by change 1 + 3 * p ≤ 4; linarith [hp.2]⟩
  · rw [Fin.sum_univ_two]
    change (1 : ℝ) * 2 * 1 + 1 * 4 * 1 < 10
    norm_num

/-!
## The exported sum does not decide congestion either

`Signature.lean` proves the single-loop scalar `σ = λ·Amax` too coarse to
decide congestion or the phase. The same limit binds the number this file
exports. A one-server star at unit fan-out has the demand operator of the
loop it wraps (`ClosedLoop.toStar`) and exports that loop's own signature
(`ClosedLoop.toStar_signature`), so the equal-signature pair of
`Signature.lean` transports to the fan-in vocabulary as a genuine pair of
stars rather than an analogy.
-/

namespace ClosedLoop

/-- **A loop as a one-server star.** Unit fan-out, the loop's response at
the single server, the loop's kernel at the sink. `aggResponse` collapses
over `Fin 1` to `λ·h`, so the star's demand operator is the loop's own
(`toStar_congestedEq_iff`). -/
noncomputable def toStar (L : ClosedLoop) : Star 1 where
  lam := ![L.lam]
  r := ![1]
  h := ![L.h]
  gD := L.g
  lam_nonneg := Fin.forall_fin_one.mpr L.lam_nonneg
  r_nonneg := Fin.forall_fin_one.mpr zero_le_one
  gD_mem := L.g_mem

/-- The embedding preserves congestion: the one-server star has a congested
equilibrium at the sink exactly when the loop it wraps has one, both sides
reading fixed points of the same operator. -/
theorem toStar_congestedEq_iff {L : ClosedLoop} {Θ : ℝ} :
    L.toStar.CongestedEq Θ ↔ L.CongestedEq Θ := by
  have hF : ∀ y, L.toStar.F y = L.F y := fun y => by
    change (∑ i : Fin 1, L.toStar.r i * L.toStar.lam i * L.toStar.h i (L.g y))
        = L.F y
    rw [Fin.sum_univ_one]
    change (1 : ℝ) * L.lam * L.h (L.g y) = L.lam * L.h (L.g y)
    ring
  unfold Star.CongestedEq BoundedLoop.CongestedEq
  exact exists_congr fun y => by rw [hF]

/-- The one-server star exports the loop's own signature: taking the loop's
response bound as its contract, `∑ σᵢ = λ·Amax`. The fan-in export and the
single-loop scalar of `Signature.lean` are the same number here. -/
theorem toStar_signature (L : ClosedLoop) :
    ∑ i, L.toStar.signature ![L.Amax] i = L.signature := by
  rw [Fin.sum_univ_one]
  change L.lam * L.Amax * 1 = L.lam * L.Amax
  ring

end ClosedLoop

/-- A verdict on a star and its declared contract *factors through the
signature sum* when it is constant on the fibers of that sum: two
contracted stars exporting the same total receive the same verdict. The
fan-in analogue of `FactorsThroughSignature`, over the number the fan-in
contract actually exports. -/
def FactorsThroughStarSignature (P : Star 1 → (Fin 1 → ℝ) → Prop) : Prop :=
  ∀ (S₁ : Star 1) (K₁ : Fin 1 → ℝ) (S₂ : Star 1) (K₂ : Fin 1 → ℝ),
    S₁.Contract K₁ → S₂.Contract K₂ →
      (∑ i, S₁.signature K₁ i) = ∑ i, S₂.signature K₂ i →
        (P S₁ K₁ ↔ P S₂ K₂)

/-- The separation principle for the exported sum: a pair of contracted
stars exporting one total that a property `Φ` separates refutes every
certificate factoring through that total — such a certificate owes the
pair one verdict, and `Φ` gives two. The fan-in mirror of
`no_signature_cert_of_separating_pair`. -/
theorem no_star_signature_cert_of_separating_pair {Φ : Star 1 → Prop}
    {S₁ S₂ : Star 1} {K₁ K₂ : Fin 1 → ℝ}
    (hK₁ : S₁.Contract K₁) (hK₂ : S₂.Contract K₂)
    (hσ : (∑ i, S₁.signature K₁ i) = ∑ i, S₂.signature K₂ i)
    (h₁ : Φ S₁) (h₂ : ¬Φ S₂) :
    ∀ P : Star 1 → (Fin 1 → ℝ) → Prop, FactorsThroughStarSignature P →
      ¬∀ (S : Star 1) (K : Fin 1 → ℝ), S.Contract K → (P S K ↔ Φ S) := by
  intro P hP hall
  exact h₂ ((hall S₂ K₂ hK₂).mp
    ((hP S₁ K₁ S₂ K₂ hK₁ hK₂ hσ).mp ((hall S₁ K₁ hK₁).mpr h₁)))

/-- **The fan-in export is incomplete too.** No certificate reading only
the exported signature sum decides congestion at the sink at threshold `3`.
The witnesses are the equal-signature pair of `Signature.lean` embedded at
one server and unit fan-out: `headroomLoop.toStar` is safe there and
`flatLoop.toStar` is congested, and both export the sum `4` under their
own response bounds as contracts.

What this does not say. The multi-server sum is not shown incomplete in
any way beyond what the one-server case already forces — the witnesses
live at `k = 1`, and a star of more servers is not examined. And
`no_congestedEq_of_signatures` stays sound and one-directional: `∑ σᵢ < Θ`
still certifies the sink for any kernel. This bounds what a contract can
*decide*; it does not weaken what a contract *certifies*. -/
theorem star_signature_not_decide_congestedEq :
    ∀ P : Star 1 → (Fin 1 → ℝ) → Prop, FactorsThroughStarSignature P →
      ¬∀ (S : Star 1) (K : Fin 1 → ℝ),
        S.Contract K → (P S K ↔ ¬S.CongestedEq 3) := by
  have hcon : ∀ L : ClosedLoop, L.toStar.Contract ![L.Amax] :=
    fun L => Fin.forall_fin_one.mpr L.h_le_Amax
  refine no_star_signature_cert_of_separating_pair
    (S₁ := headroomLoop.toStar) (K₁ := ![headroomLoop.Amax])
    (S₂ := flatLoop.toStar) (K₂ := ![flatLoop.Amax])
    (hcon headroomLoop) (hcon flatLoop) ?_ ?_ ?_
  · rw [ClosedLoop.toStar_signature, ClosedLoop.toStar_signature]
    exact headroomLoop_signature_eq_flatLoop
  · exact fun hc =>
      headroomLoop_no_congestedEq (ClosedLoop.toStar_congestedEq_iff.mp hc)
  · exact not_not_intro
      (ClosedLoop.toStar_congestedEq_iff.mpr flatLoop_congestedEq)

end Overload
