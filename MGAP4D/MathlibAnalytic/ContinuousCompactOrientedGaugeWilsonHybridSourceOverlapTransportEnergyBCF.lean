import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapCouplingKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridEndpointTransportCouplingBCF
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- The canonical source-step endpoint-pair law is a probability measure. -/
instance continuousCompactOriented_independentPairHybridEndpointPairMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (source : C.base.geometry.Edge) :
    IsProbabilityMeasure (C.independentPairHybridEndpointPairMeasure source) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
  exact Measure.isProbabilityMeasure_map
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C source).aemeasurable

/-- Retain one canonical source-step endpoint pair and, conditionally on that
pair, sample the exact overlap coupling of the two target-link conditional laws. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge) :
    Measure
      ((C.base.Configuration × C.base.Configuration) ×
        (C.base.Gauge × C.base.Gauge)) :=
  C.independentPairHybridEndpointPairMeasure source ⊗ₘ
    C.configurationPairConditionalOverlapCouplingKernel target

/-- The source-step overlap transport law is a probability measure. -/
instance continuousCompactOriented_independentPairHybridSourceOverlapTransportMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.independentPairHybridSourceOverlapTransportMeasure target source) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportMeasure
  infer_instance

/-- Squared observable transport at `target`, indexed by one source-step
configuration pair.  Both coupled target values are inserted into the first
configuration of the source pair, so the integrand vanishes on the target-value
diagonal. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Gauge × C.base.Gauge)) : ℝ :=
  (C.singleLinkConditionalOverlapObservableTransportBCF
    w.1.1 target O w.2) ^ 2

/-- The source-indexed overlap transport integrand is continuous jointly in the
background pair and the coupled target values. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridSourceOverlapTransportIntegrandBCF target O) := by
  have hLeftInput : Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          (C.base.Gauge × C.base.Gauge) =>
        (w.1.1, w.2.1)) :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)
  have hRightInput : Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          (C.base.Gauge × C.base.Gauge) =>
        (w.1.1, w.2.2)) :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd)
  have hLeft : Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          (C.base.Gauge × C.base.Gauge) =>
        C.base.replaceLink w.1.1 target w.2.1) :=
    (continuous_compact_oriented_replaceLink_uncurry C target).comp hLeftInput
  have hRight : Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          (C.base.Gauge × C.base.Gauge) =>
        C.base.replaceLink w.1.1 target w.2.2) :=
    (continuous_compact_oriented_replaceLink_uncurry C target).comp hRightInput
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF
  exact ((O.continuous.comp hLeft).sub (O.continuous.comp hRight)).pow 2

/-- The source-indexed transport integrand is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Gauge × C.base.Gauge)) :
    0 ≤ C.independentPairHybridSourceOverlapTransportIntegrandBCF target O w := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF
  exact sq_nonneg _

/-- The source-indexed transport integrand has the same universal square bound
as every fixed-background overlap transport. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (w : (C.base.Configuration × C.base.Configuration) ×
      (C.base.Gauge × C.base.Gauge)) :
    C.independentPairHybridSourceOverlapTransportIntegrandBCF target O w ≤
      (2 * ‖O‖) ^ 2 := by
  have hAbs :=
    continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_abs_le
      C w.1.1 target O w.2
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF
  have hBounds := abs_le.mp hAbs
  nlinarith [norm_nonneg O]

/-- The joint source-step overlap transport integrand is integrable. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (C.independentPairHybridSourceOverlapTransportIntegrandBCF target O)
      (C.independentPairHybridSourceOverlapTransportMeasure target source) := by
  apply continuous_compact_oriented_integrable_of_uniform_bound
    (C.independentPairHybridSourceOverlapTransportMeasure target source)
    (C.independentPairHybridSourceOverlapTransportIntegrandBCF target O)
    (continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_continuous
      C target O).stronglyMeasurable
    ((2 * ‖O‖) ^ 2)
  intro w
  rw [abs_of_nonneg
    (continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_nonneg
      C target O w)]
  exact
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_le
      C target O w

/-- Integrated target-link overlap transport energy along one canonical source
hybrid step. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ w,
    C.independentPairHybridSourceOverlapTransportIntegrandBCF target O w
    ∂C.independentPairHybridSourceOverlapTransportMeasure target source

/-- The integrated source-step overlap transport energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridSourceOverlapTransportEnergyBCF
      target source O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportEnergyBCF
  exact integral_nonneg fun w =>
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_nonneg
      C target O w

/-- Exact disintegration of the source-step transport energy into the fixed-pair
conditional overlap transport energies. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_fiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridSourceOverlapTransportEnergyBCF target source O =
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.singleLinkConditionalOverlapObservableTransportEnergyBCF
          z.1 z.2 z.1 target O
        ∂C.independentPairHybridEndpointPairMeasure source := by
  have hJoint :=
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_integrable
      C target source O
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportMeasure
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF,
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF,
      continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
    using Measure.integral_compProd hJoint

/-- A uniform Gibbs-exponent oscillation radius for the target conditional law
along the canonical source-step pair law bounds the integrated square transport
by the named compact-Haar influence coefficient. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_compactHaarOscillationInfluence_of_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc : ∀ z : C.base.Configuration × C.base.Configuration,
      ∀ u v : C.base.Gauge,
        (C.base.gibbsExponent (C.base.replaceLink z.1 target u) -
          C.base.gibbsExponent (C.base.replaceLink z.2 target u)) -
        (C.base.gibbsExponent (C.base.replaceLink z.1 target v) -
          C.base.gibbsExponent (C.base.replaceLink z.2 target v)) ≤ R) :
    C.independentPairHybridSourceOverlapTransportEnergyBCF target source O ≤
      (2 * ‖O‖) ^ 2 * compactHaarOscillationInfluence R := by
  let μ := C.independentPairHybridEndpointPairMeasure source
  let c : ℝ := (2 * ‖O‖) ^ 2 * compactHaarOscillationInfluence R
  letI : IsProbabilityMeasure μ :=
    continuousCompactOriented_independentPairHybridEndpointPairMeasure_isProbability
      C source
  have hJoint :=
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_integrable
      C target source O
  have hFiberIntegrable : Integrable
      (fun z : C.base.Configuration × C.base.Configuration =>
        C.singleLinkConditionalOverlapObservableTransportEnergyBCF
          z.1 z.2 z.1 target O) μ := by
    simpa
      [μ,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportMeasure,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF,
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF,
        continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
      using hJoint.integral_compProd
  rw [continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_fiber]
  calc
    (∫ z : C.base.Configuration × C.base.Configuration,
        C.singleLinkConditionalOverlapObservableTransportEnergyBCF
          z.1 z.2 z.1 target O ∂μ) ≤
      ∫ _z : C.base.Configuration × C.base.Configuration, c ∂μ := by
        apply integral_mono hFiberIntegrable (integrable_const c)
        intro z
        exact
          continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportEnergyBCF_le_compactHaarOscillationInfluence_of_oscillation
            C z.1 z.2 z.1 target O R hR (hOsc z)
    _ = c := by simp

end

end MathlibAnalytic
end MGAP4D