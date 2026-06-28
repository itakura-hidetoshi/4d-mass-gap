import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointDensity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Exact one-link heat-bath integration on an assembled off-link fiber is
integration over the newly sampled Haar link value with its conditional
density. -/
theorem continuous_compact_oriented_lintegral_heatBathKernel_assemble
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge)
    (Aoff : C.base.OffLinkConfiguration target)
    (F : C.base.Configuration → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ B, F B
        ∂C.singleLinkHeatBathKernel target
          (C.base.singleLinkAssemble target g Aoff) =
      ∫⁻ h,
        C.singleLinkConditionalDensity target
            (C.base.singleLinkAssemble target g Aoff) h *
          F (C.base.singleLinkAssemble target h Aoff)
        ∂normalizedCompactHaar C.base.Gauge := by
  rw [continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
      C target (C.base.singleLinkAssemble target g Aoff) F hF,
    continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  have hDensity : Measurable
      (C.singleLinkConditionalDensity target
        (C.base.singleLinkAssemble target g Aoff)) :=
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
      C target).comp measurable_prodMk_left
  have hUpdated : Measurable (fun h : C.base.Gauge =>
      F (C.base.replaceLink
        (C.base.singleLinkAssemble target g Aoff) target h)) :=
    hF.comp
      (continuous_compact_oriented_replaceLink C
        (C.base.singleLinkAssemble target g Aoff) target).measurable
  rw [lintegral_withDensity_eq_lintegral_mul
    (normalizedCompactHaar C.base.Gauge) hDensity hUpdated]
  apply lintegral_congr
  intro h
  rw [compact_oriented_replaceLink_singleLinkAssemble]
  rfl

end

end MathlibAnalytic
end MGAP4D
