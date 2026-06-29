import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathFiberIntegral

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Multiplying one exact heat-bath fiber integral by the global coordinate
Gibbs density produces integration against the symmetric joint density. -/
theorem continuous_compact_oriented_coordinateDensity_mul_lintegral_heatBathKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (Aoff : C.base.OffLinkConfiguration target)
    (F : C.base.Configuration → ℝ≥0∞)
    (hF : Measurable F) :
    C.singleLinkCoordinateGibbsDensity target (g, Aoff) *
        (∫⁻ B, F B
          ∂C.singleLinkHeatBathKernel target
            (C.base.singleLinkAssemble target g Aoff)) =
      ∫⁻ h,
        C.singleLinkJointDensity target g h Aoff *
          F (C.base.singleLinkAssemble target h Aoff)
        ∂normalizedCompactHaar C.base.Gauge := by
  rw [continuous_compact_oriented_lintegral_heatBathKernel_assemble
    C target g Aoff F hF]
  have hDensity : Measurable
      (C.singleLinkConditionalDensity target
        (C.base.singleLinkAssemble target g Aoff)) := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    apply ENNReal.measurable_ofReal.comp
    exact
      (continuous_compact_oriented_singleLinkBoltzmannFactor
        C (C.base.singleLinkAssemble target g Aoff) target).measurable.div
          measurable_const
  have hAssemble : Measurable (fun h : C.base.Gauge =>
      C.base.singleLinkAssemble target h Aoff) :=
    (C.base.singleLinkCoordinatesMeasurableEquiv target).symm.measurable.comp
      (measurable_id.prodMk measurable_const)
  have hIntegrand : Measurable (fun h : C.base.Gauge =>
      C.singleLinkConditionalDensity target
          (C.base.singleLinkAssemble target g Aoff) h *
        F (C.base.singleLinkAssemble target h Aoff)) :=
    hDensity.mul (hF.comp hAssemble)
  rw [← lintegral_const_mul _ hIntegrand]
  apply lintegral_congr
  intro h
  simp [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkJointDensity,
    mul_assoc]

end

end MathlibAnalytic
end MGAP4D
