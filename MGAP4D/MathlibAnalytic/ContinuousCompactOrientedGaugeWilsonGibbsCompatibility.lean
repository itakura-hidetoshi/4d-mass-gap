import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathReversibility
import Mathlib.MeasureTheory.Integral.Marginal

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The current physical-link replacement is exactly `Function.update` on the
finite product configuration space. -/
theorem compact_oriented_replaceLink_eq_update
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [DecidableEq C.base.geometry.Edge]
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.base.replaceLink A target g = Function.update A target g := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, he]

/-- Averaging a nonnegative measurable configuration function over one fresh
normalized-Haar link and then over the full product Haar measure preserves its
integral.  This is the one-coordinate Fubini identity needed by the current
Gibbs compatibility bridge. -/
theorem continuous_compact_oriented_configurationHaar_lintegral_singleLink_average
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ A : C.base.Configuration,
        (∫⁻ g : C.base.Gauge,
          f (C.base.replaceLink A target g)
          ∂normalizedCompactHaar C.base.Gauge)
        ∂C.base.configurationHaarMeasure) =
      ∫⁻ A : C.base.Configuration, f A
        ∂C.base.configurationHaarMeasure := by
  classical
  let μ : C.base.geometry.Edge → Measure C.base.Gauge :=
    fun _ => normalizedCompactHaar C.base.Gauge
  have hReplace : Measurable
      (fun p : C.base.Configuration × C.base.Gauge =>
        C.base.replaceLink p.1 target p.2) := by
    apply measurable_pi_iff.mpr
    intro e
    by_cases he : e = target
    · subst e
      simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
        (measurable_snd : Measurable
          (fun p : C.base.Configuration × C.base.Gauge => p.2))
    · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, he] using
        ((measurable_pi_apply e).comp
          (measurable_fst : Measurable
            (fun p : C.base.Configuration × C.base.Gauge => p.1)))
  have hJoint : Measurable
      (fun p : C.base.Configuration × C.base.Gauge =>
        f (C.base.replaceLink p.1 target p.2)) :=
    hf.comp hReplace
  have hAverage : Measurable
      (fun A : C.base.Configuration =>
        ∫⁻ g : C.base.Gauge,
          f (C.base.replaceLink A target g)
          ∂normalizedCompactHaar C.base.Gauge) :=
    hJoint.lintegral_prod_right
  change
    (∫⁻ A : C.base.Configuration,
        (∫⁻ g : C.base.Gauge,
          f (C.base.replaceLink A target g)
          ∂normalizedCompactHaar C.base.Gauge)
        ∂Measure.pi μ) =
      ∫⁻ A : C.base.Configuration, f A ∂Measure.pi μ
  apply MeasureTheory.lintegral_eq_of_lmarginal_eq
    (μ := μ) {target} hAverage hf
  ext A
  rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton]
  simp_rw [← compact_oriented_replaceLink_eq_update C]
  simp only [compact_oriented_replaceLink_replaceLink]
  simp [μ]

/-- Exact one-link conditional resampling preserves the canonical finite-volume
Wilson Gibbs integral for every nonnegative measurable observable. -/
theorem continuous_compact_oriented_gibbs_lintegral_singleLinkConditionalMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ A : C.base.Configuration,
        (∫⁻ g : C.base.Gauge,
          f (C.base.replaceLink A target g)
          ∂C.singleLinkConditionalMeasure A target)
        ∂C.gibbsMeasure) =
      ∫⁻ A : C.base.Configuration, f A ∂C.gibbsMeasure := by
  have hSymm :=
    continuous_compact_oriented_singleLinkHeatBathTransitionLIntegral_symm
      C target
      (fun z : C.base.Configuration × C.base.Configuration => f z.2)
      (hf.comp measurable_snd)
  calc
    (∫⁻ A : C.base.Configuration,
        (∫⁻ g : C.base.Gauge,
          f (C.base.replaceLink A target g)
          ∂C.singleLinkConditionalMeasure A target)
        ∂C.gibbsMeasure) =
      C.singleLinkHeatBathTransitionLIntegral target
        (fun z : C.base.Configuration × C.base.Configuration => f z.2) := by
          unfold
            ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransitionLIntegral
          apply lintegral_congr
          intro A
          exact
            (continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
              C target A f hf).symm
    _ = C.singleLinkHeatBathTransitionLIntegral target
        (fun z : C.base.Configuration × C.base.Configuration => f z.1) := by
          simpa using hSymm
    _ = ∫⁻ A : C.base.Configuration, f A ∂C.gibbsMeasure := by
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransitionLIntegral
      simp

end

end MathlibAnalytic
end MGAP4D
