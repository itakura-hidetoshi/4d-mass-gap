import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathTransitionIntegral

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Tonelli exchange of the old and newly sampled compact-group link values,
with all off-link variables retained in the middle. -/
theorem continuous_compact_oriented_lintegral_swap_old_new
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ g,
      ∫⁻ Aoff,
        ∫⁻ h, F (g, (Aoff, h))
          ∂normalizedCompactHaar C.base.Gauge
        ∂C.base.offLinkHaarMeasure target
      ∂normalizedCompactHaar C.base.Gauge) =
    ∫⁻ g,
      ∫⁻ Aoff,
        ∫⁻ h, F (h, (Aoff, g))
          ∂normalizedCompactHaar C.base.Gauge
        ∂C.base.offLinkHaarMeasure target
      ∂normalizedCompactHaar C.base.Gauge := by
  have hInner : Measurable
      (fun z : C.base.Gauge × C.base.OffLinkConfiguration target =>
        ∫⁻ h, F (z.1, (z.2, h))
          ∂normalizedCompactHaar C.base.Gauge) :=
    (hF.comp MeasurableEquiv.prodAssoc.measurable).
      lintegral_prod_right'
  calc
    (∫⁻ g,
      ∫⁻ Aoff,
        ∫⁻ h, F (g, (Aoff, h))
          ∂normalizedCompactHaar C.base.Gauge
        ∂C.base.offLinkHaarMeasure target
      ∂normalizedCompactHaar C.base.Gauge) =
      ∫⁻ Aoff,
        ∫⁻ g,
          ∫⁻ h, F (g, (Aoff, h))
            ∂normalizedCompactHaar C.base.Gauge
          ∂normalizedCompactHaar C.base.Gauge
        ∂C.base.offLinkHaarMeasure target := by
          exact lintegral_lintegral_swap hInner.aemeasurable
    _ = ∫⁻ Aoff,
        ∫⁻ h,
          ∫⁻ g, F (g, (Aoff, h))
            ∂normalizedCompactHaar C.base.Gauge
          ∂normalizedCompactHaar C.base.Gauge
        ∂C.base.offLinkHaarMeasure target := by
      apply lintegral_congr
      intro Aoff
      have hSection : Measurable
          (fun z : C.base.Gauge × C.base.Gauge =>
            F (z.1, (Aoff, z.2))) :=
        hF.comp
          (measurable_fst.prodMk
            (measurable_const.prodMk measurable_snd))
      exact lintegral_lintegral_swap hSection.aemeasurable
    _ = ∫⁻ h,
        ∫⁻ Aoff,
          ∫⁻ g, F (g, (Aoff, h))
            ∂normalizedCompactHaar C.base.Gauge
          ∂C.base.offLinkHaarMeasure target
        ∂normalizedCompactHaar C.base.Gauge := by
      have hIntegrated : Measurable
          (fun z : C.base.OffLinkConfiguration target × C.base.Gauge =>
            ∫⁻ g, F (g, z)
              ∂normalizedCompactHaar C.base.Gauge) :=
        hF.lintegral_prod_left'
      exact lintegral_lintegral_swap hIntegrated.aemeasurable
    _ = ∫⁻ g,
        ∫⁻ Aoff,
          ∫⁻ h, F (h, (Aoff, g))
            ∂normalizedCompactHaar C.base.Gauge
          ∂C.base.offLinkHaarMeasure target
        ∂normalizedCompactHaar C.base.Gauge := by
      rfl

end

end MathlibAnalytic
end MGAP4D
