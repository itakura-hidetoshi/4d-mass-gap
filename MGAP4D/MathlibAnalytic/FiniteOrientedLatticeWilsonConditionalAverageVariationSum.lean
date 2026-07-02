import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditionalCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact sum of the updated variation separates the removed target
variation from the transported Dobrushin row. -/
theorem finiteOrientedConditionalAverageUpdatedVariation_sum_eq
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (target : L.Edge) :
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageUpdatedVariation
        D variation target source) =
      (∑ source : L.Edge, variation source) - variation target +
        (∑ source : L.Edge, D.influence target source) * variation target := by
  classical
  let s : Finset L.Edge := Finset.univ.erase target
  have hVarErase :
      (∑ source in s, variation source) =
        (∑ source : L.Edge, variation source) - variation target := by
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset L.Edge))
      (f := variation) (Finset.mem_univ target)
    change (∑ source in s, variation source) + variation target =
      ∑ source : L.Edge, variation source at h
    linarith
  have hInfluenceErase :
      (∑ source in s, D.influence target source) =
        ∑ source : L.Edge, D.influence target source := by
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset L.Edge))
      (f := D.influence target) (Finset.mem_univ target)
    change (∑ source in s, D.influence target source) +
      D.influence target target =
        ∑ source : L.Edge, D.influence target source at h
    rw [D.influence_diagonal_zero target, add_zero] at h
    exact h
  calc
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageUpdatedVariation
        D variation target source) =
      (∑ source in s,
        finiteOrientedConditionalAverageUpdatedVariation
          D variation target source) +
        finiteOrientedConditionalAverageUpdatedVariation
          D variation target target := by
      symm
      exact Finset.sum_erase_add
        (s := (Finset.univ : Finset L.Edge))
        (f := fun source =>
          finiteOrientedConditionalAverageUpdatedVariation
            D variation target source)
        (Finset.mem_univ target)
    _ = ∑ source in s,
        (variation source +
          D.influence target source * variation target) := by
      rw [show finiteOrientedConditionalAverageUpdatedVariation
          D variation target target = 0 by
        simp [finiteOrientedConditionalAverageUpdatedVariation]]
      simp only [add_zero]
      apply Finset.sum_congr rfl
      intro source hsource
      have hne : source ≠ target := Finset.ne_of_mem_erase hsource
      simp [finiteOrientedConditionalAverageUpdatedVariation, hne]
    _ = (∑ source in s, variation source) +
        (∑ source in s, D.influence target source) * variation target := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = (∑ source : L.Edge, variation source) - variation target +
        (∑ source : L.Edge, D.influence target source) * variation target := by
      rw [hVarErase, hInfluenceErase]

/-- A strict Dobrushin coefficient decreases total variation by at least the
fraction `1 - c` of the variation at the updated target. -/
theorem finiteOrientedConditionalAverageUpdatedVariation_sum_le
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target : L.Edge) :
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageUpdatedVariation
        D variation target source) ≤
      (∑ source : L.Edge, variation source) -
        (1 - D.dobrushinCoefficient) * variation target := by
  rw [finiteOrientedConditionalAverageUpdatedVariation_sum_eq]
  have hRow := D.rowSum_le_coefficient target
  have hMul := mul_le_mul_of_nonneg_right hRow (hVariation target)
  nlinarith

/-- In particular, one exact conditional average never increases the total
link-variation mass. -/
theorem finiteOrientedConditionalAverageUpdatedVariation_sum_le_sum
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target : L.Edge) :
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageUpdatedVariation
        D variation target source) ≤
      ∑ source : L.Edge, variation source := by
  have hDecrease :=
    finiteOrientedConditionalAverageUpdatedVariation_sum_le
      D variation hVariation target
  have hGap : 0 ≤ 1 - D.dobrushinCoefficient := by
    linarith [D.dobrushinCoefficient_lt_one]
  have hRemoved :
      0 ≤ (1 - D.dobrushinCoefficient) * variation target :=
    mul_nonneg hGap (hVariation target)
  linarith

/-- If the current target has positive variation, the total variation mass
strictly decreases after its exact conditional average. -/
theorem finiteOrientedConditionalAverageUpdatedVariation_sum_lt_sum
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target : L.Edge)
    (hTarget : 0 < variation target) :
    (∑ source : L.Edge,
      finiteOrientedConditionalAverageUpdatedVariation
        D variation target source) <
      ∑ source : L.Edge, variation source := by
  have hDecrease :=
    finiteOrientedConditionalAverageUpdatedVariation_sum_le
      D variation hVariation target
  have hGap : 0 < 1 - D.dobrushinCoefficient := by
    linarith [D.dobrushinCoefficient_lt_one]
  have hRemoved :
      0 < (1 - D.dobrushinCoefficient) * variation target :=
    mul_pos hGap hTarget
  linarith

end

end MathlibAnalytic
end MGAP4D
