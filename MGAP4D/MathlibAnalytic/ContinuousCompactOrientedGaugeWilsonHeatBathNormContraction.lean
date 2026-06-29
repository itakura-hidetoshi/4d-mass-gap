import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathLinearProjection

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

theorem continuous_compact_oriented_singleLinkHeatBathProjection_abs_le_norm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |C.singleLinkHeatBathProjection target O A| ≤ ‖O‖ := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  have hObservable :=
    continuous_compact_oriented_singleLinkObservable_integrable C O A target
  have hAbs : Integrable
      (fun g : C.base.Gauge =>
        |O (C.base.replaceLink A target g)|)
      (C.singleLinkConditionalMeasure A target) := by
    simpa [Real.norm_eq_abs] using hObservable.norm
  have hConst : Integrable
      (fun _ : C.base.Gauge => ‖O‖)
      (C.singleLinkConditionalMeasure A target) :=
    integrable_const ‖O‖
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  calc
    |∫ g : C.base.Gauge,
        O (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target| ≤
      ∫ g : C.base.Gauge,
        |O (C.base.replaceLink A target g)|
        ∂C.singleLinkConditionalMeasure A target :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _g : C.base.Gauge, ‖O‖
        ∂C.singleLinkConditionalMeasure A target := by
      apply integral_mono hAbs hConst
      intro g
      simpa [Real.norm_eq_abs] using
        O.norm_coe_le_norm (C.base.replaceLink A target g)
    _ = ‖O‖ := by simp

theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCF_norm_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    ‖C.singleLinkHeatBathProjectionBCF target O‖ ≤ ‖O‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg O)).2
  intro A
  simpa [Real.norm_eq_abs] using
    continuous_compact_oriented_singleLinkHeatBathProjection_abs_le_norm
      C target O A

end
end MathlibAnalytic
end MGAP4D
