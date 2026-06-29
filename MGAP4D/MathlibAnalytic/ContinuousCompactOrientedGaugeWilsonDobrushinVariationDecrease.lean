import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationSum

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

theorem continuous_compact_oriented_dobrushinUpdatedVariation_total_le
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (target : C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target) ≤
      continuousCompactOrientedGaugeWilsonTotalVariation variation -
        (1 - D.dobrushinCoefficient) * variation target := by
  have hRowMul :
      (∑ source : C.base.geometry.Edge, D.influence target source) *
          variation target ≤
        D.dobrushinCoefficient * variation target :=
    mul_le_mul_of_nonneg_right
      (D.rowSum_le_coefficient target) (hVariation target)
  unfold continuousCompactOrientedGaugeWilsonTotalVariation
  rw [continuous_compact_oriented_dobrushinUpdatedVariation_sum_eq]
  calc
    (∑ source : C.base.geometry.Edge, variation source) +
          (∑ source : C.base.geometry.Edge, D.influence target source) *
            variation target - variation target ≤
      (∑ source : C.base.geometry.Edge, variation source) +
          D.dobrushinCoefficient * variation target - variation target :=
      sub_le_sub_right (add_le_add (le_refl _) hRowMul) _
    _ = (∑ source : C.base.geometry.Edge, variation source) -
        (1 - D.dobrushinCoefficient) * variation target := by ring

end
end MathlibAnalytic
end MGAP4D
