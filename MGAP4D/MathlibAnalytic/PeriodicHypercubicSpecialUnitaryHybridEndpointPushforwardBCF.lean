import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridCenteredL2TransportBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Pre-step endpoint map of the canonical independent Gibbs-pair hybrid path. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration → C.base.Configuration :=
  fun z =>
    C.independentPairHybridConfiguration z.1 z.2
      (C.canonicalEdgeOrder target).val

/-- Post-step endpoint map of the canonical independent Gibbs-pair hybrid path. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration → C.base.Configuration :=
  fun z =>
    C.independentPairHybridConfiguration z.1 z.2
      ((C.canonicalEdgeOrder target).val + 1)

/-- The pre-step hybrid endpoint map is continuous. -/
theorem continuous_compact_oriented_independentPairHybridPreEndpointMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.independentPairHybridPreEndpointMap target) := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap]
    using
      continuous_compact_oriented_independentPairHybridConfiguration
        C (C.canonicalEdgeOrder target).val

/-- The post-step hybrid endpoint map is continuous. -/
theorem continuous_compact_oriented_independentPairHybridPostEndpointMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.independentPairHybridPostEndpointMap target) := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap]
    using
      continuous_compact_oriented_independentPairHybridConfiguration
        C ((C.canonicalEdgeOrder target).val + 1)

/-- The pre-step hybrid endpoint map is measurable. -/
theorem continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.independentPairHybridPreEndpointMap target) :=
  (continuous_compact_oriented_independentPairHybridPreEndpointMap_continuous
    C target).measurable

/-- The post-step hybrid endpoint map is measurable. -/
theorem continuous_compact_oriented_independentPairHybridPostEndpointMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.independentPairHybridPostEndpointMap target) :=
  (continuous_compact_oriented_independentPairHybridPostEndpointMap_continuous
    C target).measurable

/-- Pushforward law of the pre-step endpoint under two independent Gibbs
configurations. This measure is not asserted to equal the Gibbs measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) : Measure C.base.Configuration :=
  Measure.map (C.independentPairHybridPreEndpointMap target)
    (C.gibbsMeasure.prod C.gibbsMeasure)

/-- Pushforward law of the post-step endpoint under two independent Gibbs
configurations. This measure is not asserted to equal the Gibbs measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) : Measure C.base.Configuration :=
  Measure.map (C.independentPairHybridPostEndpointMap target)
    (C.gibbsMeasure.prod C.gibbsMeasure)

/-- Integrate a strongly measurable observable against the pre-step endpoint
pushforward law. -/
theorem continuous_compact_oriented_integral_independentPairHybridPreEndpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ A, f A ∂C.independentPairHybridPreEndpointMeasure target) =
      ∫ z, f (C.independentPairHybridPreEndpointMap target z)
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
  exact MeasureTheory.integral_map
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
      C target).aemeasurable
    hf.aestronglyMeasurable

/-- Integrate a strongly measurable observable against the post-step endpoint
pushforward law. -/
theorem continuous_compact_oriented_integral_independentPairHybridPostEndpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ A, f A ∂C.independentPairHybridPostEndpointMeasure target) =
      ∫ z, f (C.independentPairHybridPostEndpointMap target z)
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMeasure
  exact MeasureTheory.integral_map
    (continuous_compact_oriented_independentPairHybridPostEndpointMap_measurable
      C target).aemeasurable
    hf.aestronglyMeasurable

/-- The pre-step centered endpoint energy is exactly the native heat-bath
fluctuation energy under the pre-step endpoint pushforward law. -/
theorem continuous_compact_oriented_independentPairHybridPreCenteredEnergyBCF_eq_endpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridPreCenteredEnergyBCF target O =
      ∫ A, (C.singleLinkHeatBathFluctuation target O A) ^ 2
        ∂C.independentPairHybridPreEndpointMeasure target := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  have hSquare : StronglyMeasurable
      (fun A => (C.singleLinkHeatBathFluctuation target O A) ^ 2) := by
    simpa [pow_two] using hFluctuation.mul hFluctuation
  symm
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredEnergyBCF,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreCenteredBCF,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap]
    using
      continuous_compact_oriented_integral_independentPairHybridPreEndpointMeasure
        C target
          (fun A => (C.singleLinkHeatBathFluctuation target O A) ^ 2)
          hSquare

/-- The post-step centered endpoint energy is exactly the native heat-bath
fluctuation energy under the post-step endpoint pushforward law. -/
theorem continuous_compact_oriented_independentPairHybridPostCenteredEnergyBCF_eq_endpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridPostCenteredEnergyBCF target O =
      ∫ A, (C.singleLinkHeatBathFluctuation target O A) ^ 2
        ∂C.independentPairHybridPostEndpointMeasure target := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  have hSquare : StronglyMeasurable
      (fun A => (C.singleLinkHeatBathFluctuation target O A) ^ 2) := by
    simpa [pow_two] using hFluctuation.mul hFluctuation
  symm
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredEnergyBCF,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostCenteredBCF,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap]
    using
      continuous_compact_oriented_integral_independentPairHybridPostEndpointMeasure
        C target
          (fun A => (C.singleLinkHeatBathFluctuation target O A) ^ 2)
          hSquare

end

end MathlibAnalytic
end MGAP4D
