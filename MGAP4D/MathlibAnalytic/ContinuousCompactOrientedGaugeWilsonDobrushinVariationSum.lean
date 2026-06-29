import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

def continuousCompactOrientedGaugeWilsonTotalVariation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (variation : C.base.geometry.Edge → ℝ) : ℝ :=
  ∑ e : C.base.geometry.Edge, variation e

theorem continuous_compact_oriented_dobrushinUpdatedVariation_sum_eq
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (target : C.base.geometry.Edge) :
    (∑ source : C.base.geometry.Edge,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source) =
      (∑ source : C.base.geometry.Edge, variation source) +
        (∑ source : C.base.geometry.Edge, D.influence target source) *
          variation target - variation target := by
  classical
  have hPointwise (source : C.base.geometry.Edge) :
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source =
        variation source + D.influence target source * variation target -
          (if source = target then variation target else 0) := by
    by_cases h : source = target
    · subst source
      simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation,
        D.influence_diagonal_zero]
    · simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation, h]
  calc
    (∑ source : C.base.geometry.Edge,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source) =
      ∑ source : C.base.geometry.Edge,
        (variation source + D.influence target source * variation target -
          (if source = target then variation target else 0)) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      exact hPointwise source
    _ = (∑ source : C.base.geometry.Edge, variation source) +
        (∑ source : C.base.geometry.Edge, D.influence target source) *
          variation target - variation target := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_mul]
      simp

end
end MathlibAnalytic
end MGAP4D
