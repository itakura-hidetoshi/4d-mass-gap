import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointMeasurable

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Exact compact-group one-link heat-bath resampling is reversible for the
orientation-correct Wilson Gibbs law, expressed as symmetry of every
nonnegative measurable transition observable. -/
theorem continuous_compact_oriented_singleLinkHeatBathTransitionLIntegral_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (Phi : C.base.Configuration × C.base.Configuration → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    C.singleLinkHeatBathTransitionLIntegral target Phi =
      C.singleLinkHeatBathTransitionLIntegral target
        (fun z => Phi z.swap) := by
  rw [continuous_compact_oriented_singleLinkHeatBathTransitionLIntegral_eq_jointFubini
      C target Phi hPhi,
    continuous_compact_oriented_singleLinkHeatBathTransitionLIntegral_eq_jointFubini
      C target (fun z => Phi z.swap)
      (hPhi.comp measurable_swap)]
  let F : C.base.Gauge ×
      (C.base.OffLinkConfiguration target × C.base.Gauge) → ℝ≥0∞ :=
    fun z =>
      C.singleLinkJointDensity target z.1 z.2.2 z.2.1 *
        Phi
          (C.base.singleLinkAssemble target z.1 z.2.1,
            C.base.singleLinkAssemble target z.2.2 z.2.1)
  have hF : Measurable F :=
    (measurable_compact_oriented_singleLinkJointDensity C target).mul
      (measurable_compact_oriented_transitionObservable_assembled
        C target Phi hPhi)
  calc
    (∫⁻ g,
      ∫⁻ Aoff,
        ∫⁻ h,
          C.singleLinkJointDensity target g h Aoff *
            Phi
              (C.base.singleLinkAssemble target g Aoff,
                C.base.singleLinkAssemble target h Aoff)
          ∂normalizedCompactHaar C.base.Gauge
        ∂C.base.offLinkHaarMeasure target
      ∂normalizedCompactHaar C.base.Gauge) =
      ∫⁻ g,
        ∫⁻ Aoff,
          ∫⁻ h, F (g, (Aoff, h))
            ∂normalizedCompactHaar C.base.Gauge
          ∂C.base.offLinkHaarMeasure target
        ∂normalizedCompactHaar C.base.Gauge := by
          rfl
    _ = ∫⁻ g,
        ∫⁻ Aoff,
          ∫⁻ h, F (h, (Aoff, g))
            ∂normalizedCompactHaar C.base.Gauge
          ∂C.base.offLinkHaarMeasure target
        ∂normalizedCompactHaar C.base.Gauge :=
      continuous_compact_oriented_lintegral_swap_old_new
        C target F hF
    _ = ∫⁻ g,
        ∫⁻ Aoff,
          ∫⁻ h,
            C.singleLinkJointDensity target g h Aoff *
              (fun z => Phi z.swap)
                (C.base.singleLinkAssemble target g Aoff,
                  C.base.singleLinkAssemble target h Aoff)
            ∂normalizedCompactHaar C.base.Gauge
          ∂C.base.offLinkHaarMeasure target
        ∂normalizedCompactHaar C.base.Gauge := by
      apply lintegral_congr
      intro g
      apply lintegral_congr
      intro Aoff
      apply lintegral_congr
      intro h
      change
        C.singleLinkJointDensity target h g Aoff *
            Phi
              (C.base.singleLinkAssemble target h Aoff,
                C.base.singleLinkAssemble target g Aoff) =
          C.singleLinkJointDensity target g h Aoff *
            Phi
              (C.base.singleLinkAssemble target h Aoff,
                C.base.singleLinkAssemble target g Aoff)
      rw [continuous_compact_oriented_singleLinkJointDensity_symm]

end

end MathlibAnalytic
end MGAP4D
