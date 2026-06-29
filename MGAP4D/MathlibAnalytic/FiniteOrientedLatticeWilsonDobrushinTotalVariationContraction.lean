import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinVariationProfile

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

def finiteOrientedLatticeWilsonTotalVariation
    {L : FiniteOrientedLatticeWilsonSystem}
    (variation : L.Edge → ℝ) : ℝ :=
  ∑ e : L.Edge, variation e

theorem finite_oriented_dobrushinUpdatedVariation_sum_eq
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (target : L.Edge) :
    (∑ source : L.Edge,
        finiteOrientedLatticeWilsonDobrushinUpdatedVariation
          D variation target source) =
      (∑ source : L.Edge, variation source) +
        (∑ source : L.Edge, D.influence target source) *
          variation target - variation target := by
  classical
  have hPointwise (source : L.Edge) :
      finiteOrientedLatticeWilsonDobrushinUpdatedVariation
          D variation target source =
        variation source + D.influence target source * variation target -
          (if source = target then variation target else 0) := by
    by_cases h : source = target
    · subst source
      simp [finiteOrientedLatticeWilsonDobrushinUpdatedVariation,
        D.influence_diagonal_zero]
    · simp [finiteOrientedLatticeWilsonDobrushinUpdatedVariation, h]
  calc
    (∑ source : L.Edge,
        finiteOrientedLatticeWilsonDobrushinUpdatedVariation
          D variation target source) =
      ∑ source : L.Edge,
        (variation source + D.influence target source * variation target -
          (if source = target then variation target else 0)) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      exact hPointwise source
    _ = (∑ source : L.Edge, variation source) +
        (∑ source : L.Edge, D.influence target source) *
          variation target - variation target := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_mul]
      simp

theorem finite_oriented_dobrushinUpdatedVariation_total_le
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (target : L.Edge) :
    finiteOrientedLatticeWilsonTotalVariation
        (finiteOrientedLatticeWilsonDobrushinUpdatedVariation
          D variation target) ≤
      finiteOrientedLatticeWilsonTotalVariation variation -
        (1 - D.dobrushinCoefficient) * variation target := by
  have hRowMul :
      (∑ source : L.Edge, D.influence target source) * variation target ≤
        D.dobrushinCoefficient * variation target :=
    mul_le_mul_of_nonneg_right
      (D.rowSum_le_coefficient target) (hVariation target)
  unfold finiteOrientedLatticeWilsonTotalVariation
  rw [finite_oriented_dobrushinUpdatedVariation_sum_eq]
  calc
    (∑ source : L.Edge, variation source) +
          (∑ source : L.Edge, D.influence target source) *
            variation target - variation target ≤
      (∑ source : L.Edge, variation source) +
          D.dobrushinCoefficient * variation target - variation target :=
      sub_le_sub_right (add_le_add (le_refl _) hRowMul) _
    _ = (∑ source : L.Edge, variation source) -
        (1 - D.dobrushinCoefficient) * variation target := by ring

end
end MathlibAnalytic
end MGAP4D
