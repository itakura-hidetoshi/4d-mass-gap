import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointFiberIntegral

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Gibbs-weighted forward transition integral for one exact compact-group
heat-bath update. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransitionLIntegral
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (Phi : C.base.Configuration × C.base.Configuration → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ A,
    ∫⁻ B, Phi (A, B) ∂C.singleLinkHeatBathKernel target A
    ∂C.gibbsMeasure

/-- The Gibbs-weighted one-link transition integral is exactly the triple Haar
integral of the symmetric joint density over old link value, off-link
configuration, and newly sampled link value. -/
theorem continuous_compact_oriented_singleLinkHeatBathTransitionLIntegral_eq_jointFubini
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (Phi : C.base.Configuration × C.base.Configuration → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    C.singleLinkHeatBathTransitionLIntegral target Phi =
      ∫⁻ g,
        ∫⁻ Aoff,
          ∫⁻ h,
            C.singleLinkJointDensity target g h Aoff *
              Phi
                (C.base.singleLinkAssemble target g Aoff,
                  C.base.singleLinkAssemble target h Aoff)
            ∂normalizedCompactHaar C.base.Gauge
          ∂C.base.offLinkHaarMeasure target
        ∂normalizedCompactHaar C.base.Gauge := by
  have hOuter : Measurable (fun A : C.base.Configuration =>
      ∫⁻ B, Phi (A, B) ∂C.singleLinkHeatBathKernel target A) :=
    hPhi.lintegral_kernel_prod_right'
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransitionLIntegral
  rw [continuous_compact_oriented_lintegral_gibbs_eq_singleLinkFubini
    C target
    (fun A : C.base.Configuration =>
      ∫⁻ B, Phi (A, B) ∂C.singleLinkHeatBathKernel target A)
    hOuter]
  apply lintegral_congr
  intro g
  apply lintegral_congr
  intro Aoff
  have hSection : Measurable (fun B : C.base.Configuration =>
      Phi (C.base.singleLinkAssemble target g Aoff, B)) :=
    hPhi.comp (measurable_const.prodMk measurable_id)
  exact
    continuous_compact_oriented_coordinateDensity_mul_lintegral_heatBathKernel
      C target g Aoff
      (fun B : C.base.Configuration =>
        Phi (C.base.singleLinkAssemble target g Aoff, B))
      hSection

end

end MathlibAnalytic
end MGAP4D
