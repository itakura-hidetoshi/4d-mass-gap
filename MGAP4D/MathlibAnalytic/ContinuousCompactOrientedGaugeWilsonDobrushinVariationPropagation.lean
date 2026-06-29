import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinLocalExpectationComparison

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A centered compact fiber profile gives the sharp Dobrushin variation update
for one exact conditional expectation. -/
theorem continuous_compact_oriented_dobrushin_centeredVariation_conditionalExpectation_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (target source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source) :
    |C.singleLinkConditionalExpectation O A target -
        C.singleLinkConditionalExpectation O B target| ≤
      P.variation source +
        D.influence target source * P.variation target := by
  have hSourceBound : ∀ g : C.base.Gauge,
      |O (C.base.replaceLink A target g) -
        O (C.base.replaceLink B target g)| ≤ P.variation source := by
    intro g
    exact P.variation_bound source
      (C.base.replaceLink A target g)
      (C.base.replaceLink B target g)
      (compact_oriented_replaceLink_agreeOffLink
        C.base A B target source g hAgree)
  have hRadiusNonneg : 0 ≤ P.variation target / 2 :=
    div_nonneg (P.variation_nonneg target) (by norm_num)
  calc
    |C.singleLinkConditionalExpectation O A target -
        C.singleLinkConditionalExpectation O B target| ≤
      P.variation source +
        2 * D.influence target source * (P.variation target / 2) :=
      continuous_compact_oriented_dobrushin_singleLinkConditionalExpectation_difference_abs_le
        C D target source A B hAgree O
        (P.variation source) (P.variation target / 2)
        (P.fiberCenter B target)
        (P.variation_nonneg source)
        hSourceBound hRadiusNonneg
        (P.fiber_radius_bound B target)
    _ = P.variation source +
        D.influence target source * P.variation target := by ring

/-- Package the exact compact one-link heat-bath projection with its updated
physical-link variation bound. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.heatBathProjectionVariationBound
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target : C.base.geometry.Edge) :
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (C.singleLinkHeatBathProjectionBCF target O) := by
  classical
  refine
    { variation := continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D P.variation target
      variation_nonneg :=
        continuous_compact_oriented_dobrushinUpdatedVariation_nonneg
          D P.variation P.variation_nonneg target
      variation_bound := ?_ }
  intro source A B hAgree
  by_cases h : source = target
  · subst source
    have hEq :=
      continuous_compact_oriented_singleLinkHeatBathProjection_eq_of_agreeOffLink
        C O A B target hAgree
    change
      |C.singleLinkHeatBathProjection target O A -
        C.singleLinkHeatBathProjection target O B| ≤
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D P.variation target target
    rw [hEq]
    simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation]
  · change
      |C.singleLinkConditionalExpectation O A target -
        C.singleLinkConditionalExpectation O B target| ≤
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D P.variation target source
    simpa [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation, h] using
      (continuous_compact_oriented_dobrushin_centeredVariation_conditionalExpectation_difference_abs_le
        C D O P target source A B hAgree)

end
end MathlibAnalytic
end MGAP4D
