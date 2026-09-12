import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkGibbsPushforward

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Rewrite a nonnegative Gibbs integral in selected-link/off-link coordinates. -/
theorem continuous_compact_oriented_lintegral_gibbs_eq_singleLinkCoordinates
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F : C.base.Configuration → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ A, F A ∂C.gibbsMeasure =
      ∫⁻ z,
        C.singleLinkCoordinateGibbsDensity target z *
          F ((C.base.singleLinkCoordinatesMeasurableEquiv target).symm z)
        ∂((normalizedCompactHaar C.base.Gauge).prod
          (C.base.offLinkHaarMeasure target)) := by
  let e := C.base.singleLinkCoordinatesMeasurableEquiv target
  let μ := (normalizedCompactHaar C.base.Gauge).prod
    (C.base.offLinkHaarMeasure target)
  calc
    ∫⁻ A, F A ∂C.gibbsMeasure =
        ∫⁻ z, F (e.symm z) ∂Measure.map e C.gibbsMeasure := by
      rw [MeasureTheory.lintegral_map_equiv]
      simp [e]
    _ = ∫⁻ z, F (e.symm z)
        ∂μ.withDensity (C.singleLinkCoordinateGibbsDensity target) := by
      rw [continuous_compact_oriented_map_singleLinkCoordinates_gibbsMeasure]
    _ = ∫⁻ z,
        C.singleLinkCoordinateGibbsDensity target z * F (e.symm z) ∂μ := by
      simpa only [Function.comp_apply] using
        (lintegral_withDensity_eq_lintegral_mul μ
          (continuous_compact_oriented_singleLinkCoordinateGibbsDensity_measurable
            C target)
          (hF.comp e.symm.measurable))
    _ = _ := by rfl

/-- Fubini form of the selected-link/off-link Gibbs integral. -/
theorem continuous_compact_oriented_lintegral_gibbs_eq_singleLinkFubini
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (F : C.base.Configuration → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ A, F A ∂C.gibbsMeasure =
      ∫⁻ g,
        ∫⁻ Aoff,
          C.singleLinkCoordinateGibbsDensity target (g, Aoff) *
            F (C.base.singleLinkAssemble target g Aoff)
          ∂C.base.offLinkHaarMeasure target
        ∂normalizedCompactHaar C.base.Gauge := by
  letI : IsProbabilityMeasure (C.base.offLinkHaarMeasure target) := by
    classical
    unfold CompactOrientedGaugeWilsonSystem.offLinkHaarMeasure
    infer_instance
  rw [continuous_compact_oriented_lintegral_gibbs_eq_singleLinkCoordinates
    C target F hF]
  have hIntegrand : Measurable
      (fun z : C.base.Gauge × C.base.OffLinkConfiguration target =>
        C.singleLinkCoordinateGibbsDensity target z *
          F ((C.base.singleLinkCoordinatesMeasurableEquiv target).symm z)) :=
    (continuous_compact_oriented_singleLinkCoordinateGibbsDensity_measurable
      C target).mul
      (hF.comp
        (C.base.singleLinkCoordinatesMeasurableEquiv target).symm.measurable)
  rw [MeasureTheory.lintegral_prod _ hIntegrand.aemeasurable]
  rfl

end

end MathlibAnalytic
end MGAP4D
