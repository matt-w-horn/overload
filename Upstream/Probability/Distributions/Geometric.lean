/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Geometric

/-!
# Head and tail mass of the geometric distribution

The two lemmas mathlib PR 45786 adds to `Mathlib.Probability.Distributions.Geometric`, copied
verbatim. The rest of that file is already in mathlib.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {p : unitInterval}

/-- Head mass of the geometric distribution: `Iio m` has probability `1 - (1 - p) ^ m`. -/
lemma geometricMeasure_Iio (hp : p ≠ 0) (m : ℕ) :
    geometricMeasure p (Iio m) = ENNReal.ofReal (1 - (1 - p) ^ m) := by
  have hset : (Iio m : Set ℕ) = ⋃ k ∈ Finset.range m, {k} := by
    ext n
    simp
  rw [hset,
    measure_biUnion_finset (fun i _ j _ hij ↦ disjoint_singleton.mpr hij) fun _ _ ↦ .of_discrete,
    Finset.sum_congr rfl fun n _ ↦ geometricMeasure_singleton hp n,
    ← ENNReal.ofReal_sum_of_nonneg fun n _ ↦ geometricMeasure_nonneg p n, ← Finset.sum_mul]
  congr 1
  linear_combination (-1 : ℝ) * geom_sum_mul (1 - (p : ℝ)) m

/-- Tail mass of the geometric distribution: `Ici m` has probability `(1 - p) ^ m`. -/
lemma geometricMeasure_Ici (hp : p ≠ 0) (m : ℕ) :
    geometricMeasure p (Ici m) = ENNReal.ofReal ((1 - p) ^ m) := by
  have hle : (1 - p : ℝ) ^ m ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr p.2.2) (sub_le_self _ p.2.1)
  rw [← compl_Iio, measure_compl .of_discrete (measure_ne_top _ _), measure_univ,
    geometricMeasure_Iio hp, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sub_nonneg.mpr hle)]
  congr 1
  ring

end ProbabilityTheory
