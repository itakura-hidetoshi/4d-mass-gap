import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationDecrease

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Linkwise variation profile obtained by averaging all exact compact
single-link Dobrushin updates. -/
noncomputable def continuousCompactOrientedGaugeWilsonRandomScanUpdatedVariation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (source : C.base.geometry.Edge) : ℝ :=
  (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
    ∑ target : C.base.geometry.Edge,
      continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D variation target source

/-- The averaged compact Dobrushin variation profile is nonnegative. -/
theorem continuous_compact_oriented_randomScanUpdatedVariation_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (source : C.base.geometry.Edge) :
    0 ≤ continuousCompactOrientedGaugeWilsonRandomScanUpdatedVariation
      D variation source := by
  unfold continuousCompactOrientedGaugeWilsonRandomScanUpdatedVariation
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun target _ =>
      continuous_compact_oriented_dobrushinUpdatedVariation_nonneg
        D variation hVariation target source)

/-- A centered compact variation profile induces a concrete variation bound
for the exact random-scan heat-bath observable. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.randomScanVariationBound
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) :
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (C.randomScanHeatBathSweepBCF O) := by
  classical
  refine
    { variation := continuousCompactOrientedGaugeWilsonRandomScanUpdatedVariation
        D P.variation
      variation_nonneg :=
        continuous_compact_oriented_randomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := ?_ }
  intro source A B hAgree
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hinv : 0 ≤ n⁻¹ := by positivity
  change
    |n⁻¹ * (∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathProjection target O A) -
      n⁻¹ * (∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathProjection target O B)| ≤
      n⁻¹ * ∑ target : C.base.geometry.Edge,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D P.variation target source
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hinv]
  calc
    n⁻¹ * |∑ target : C.base.geometry.Edge,
        (C.singleLinkHeatBathProjection target O A -
          C.singleLinkHeatBathProjection target O B)| ≤
      n⁻¹ * ∑ target : C.base.geometry.Edge,
        |C.singleLinkHeatBathProjection target O A -
          C.singleLinkHeatBathProjection target O B| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs Finset.univ
          (fun target : C.base.geometry.Edge =>
            C.singleLinkHeatBathProjection target O A -
              C.singleLinkHeatBathProjection target O B)) hinv
    _ ≤ n⁻¹ * ∑ target : C.base.geometry.Edge,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D P.variation target source := by
      apply mul_le_mul_of_nonneg_left _ hinv
      apply Finset.sum_le_sum
      intro target _htarget
      exact
        (P.heatBathProjectionVariationBound D target).variation_bound
          source A B hAgree

end
end MathlibAnalytic
end MGAP4D
