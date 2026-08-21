import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointIntegralSymmetry
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

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

/-- Bochner integration of a bounded continuous observable against the actual
one-link heat-bath kernel is exactly the current pointwise conditional
expectation. -/
theorem continuous_compact_oriented_integral_singleLinkHeatBathKernel_BCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ B : C.base.Configuration, O B
        ∂C.singleLinkHeatBathKernel target A) =
      C.singleLinkConditionalExpectationBCF O A target := by
  rw [continuous_compact_oriented_singleLinkHeatBathKernel_apply]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationBCF
  exact MeasureTheory.integral_map
    (continuous_compact_oriented_replaceLink C A target).measurable.aemeasurable
    O.continuous.measurable.aestronglyMeasurable

/-- The current exact one-link conditional expectation preserves the ordinary
real integral of every bounded continuous observable under the canonical
finite-volume Wilson Gibbs law. -/
theorem continuous_compact_oriented_gibbs_integral_singleLinkConditionalExpectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ A : C.base.Configuration,
        C.singleLinkConditionalExpectationBCF O A target
        ∂C.gibbsMeasure) =
      ∫ A : C.base.Configuration, O A ∂C.gibbsMeasure := by
  let J := C.singleLinkHeatBathJointMeasure target
  have hNewContinuous : Continuous
      (fun z : C.base.Configuration × C.base.Configuration => O z.2) :=
    O.continuous.comp continuous_snd
  have hOldContinuous : Continuous
      (fun z : C.base.Configuration × C.base.Configuration => O z.1) :=
    O.continuous.comp continuous_fst
  have hNewIntegrable : Integrable
      (fun z : C.base.Configuration × C.base.Configuration => O z.2) J :=
    hNewContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOldIntegrable : Integrable
      (fun z : C.base.Configuration × C.base.Configuration => O z.1) J :=
    hOldContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hNewFubini :
      (∫ z, O z.2 ∂J) =
        ∫ A : C.base.Configuration,
          ∫ B : C.base.Configuration, O B
            ∂C.singleLinkHeatBathKernel target A
          ∂C.gibbsMeasure := by
    unfold J ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
    exact MeasureTheory.Measure.integral_compProd hNewIntegrable
  have hOldFubini :
      (∫ z, O z.1 ∂J) =
        ∫ A : C.base.Configuration,
          ∫ _B : C.base.Configuration, O A
            ∂C.singleLinkHeatBathKernel target A
          ∂C.gibbsMeasure := by
    unfold J ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
    exact MeasureTheory.Measure.integral_compProd hOldIntegrable
  have hSymm :=
    continuous_compact_oriented_integral_singleLinkHeatBathJointMeasure_symm
      C target
      (fun z : C.base.Configuration × C.base.Configuration => O z.2)
      hNewContinuous.measurable.aestronglyMeasurable
  calc
    (∫ A : C.base.Configuration,
        C.singleLinkConditionalExpectationBCF O A target
        ∂C.gibbsMeasure) =
      ∫ A : C.base.Configuration,
        ∫ B : C.base.Configuration, O B
          ∂C.singleLinkHeatBathKernel target A
        ∂C.gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact
        (continuous_compact_oriented_integral_singleLinkHeatBathKernel_BCF
          C target A O).symm
    _ = ∫ z, O z.2 ∂J := hNewFubini.symm
    _ = ∫ z, O z.1 ∂J := by simpa using hSymm
    _ = ∫ A : C.base.Configuration,
        ∫ _B : C.base.Configuration, O A
          ∂C.singleLinkHeatBathKernel target A
        ∂C.gibbsMeasure := hOldFubini
    _ = ∫ A : C.base.Configuration, O A ∂C.gibbsMeasure := by
      simp

end

end MathlibAnalytic
end MGAP4D
