import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridEndpointTransportCouplingBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalPairVarianceBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathStationarity
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Replace the same background target link by two independently supplied
compact-group values. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.base.Gauge × C.base.Gauge →
      C.base.Configuration × C.base.Configuration :=
  fun z =>
    (C.base.replaceLink A target z.1,
      C.base.replaceLink A target z.2)

/-- The native conditional-pair configuration map is continuous. -/
theorem continuous_compact_oriented_singleLinkConditionalPairConfigurationMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkConditionalPairConfigurationMap A target) := by
  exact
    ((continuous_compact_oriented_replaceLink C A target).comp
      continuous_fst).prodMk
      ((continuous_compact_oriented_replaceLink C A target).comp
        continuous_snd)

/-- Given one Gibbs background, draw two independent exact one-link heat-bath
updates.  This is the native conditional-pair reference kernel on the same
configuration-pair carrier used by the hybrid endpoint transport plan. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel C.base.Configuration
      (C.base.Configuration × C.base.Configuration) :=
  C.singleLinkHeatBathKernel target ×ₖ
    C.singleLinkHeatBathKernel target

/-- The native independent conditional-pair kernel is Markov. -/
instance continuousCompactOriented_singleLinkHeatBathIndependentPairKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.singleLinkHeatBathIndependentPairKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairKernel
  infer_instance

/-- Pointwise, the native configuration-pair kernel is the pushforward of two
independent samples from the exact compact-Haar conditional law. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathIndependentPairKernel target A =
      Measure.map
        (C.singleLinkConditionalPairConfigurationMap A target)
        ((C.singleLinkConditionalMeasure A target).prod
          (C.singleLinkConditionalMeasure A target)) := by
  letI : IsProbabilityMeasure
      (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairKernel
  rw [Kernel.prod_apply,
    continuous_compact_oriented_singleLinkHeatBathKernel_apply]
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap,
      Prod.map]
    using
      (Measure.map_prod_map
        (C.singleLinkConditionalMeasure A target)
        (C.singleLinkConditionalMeasure A target)
        (continuous_compact_oriented_replaceLink C A target).measurable
        (continuous_compact_oriented_replaceLink C A target).measurable)

/-- The observable square-difference energy under the native pair kernel is
exactly the previously constructed conditional independent-pair energy. -/
theorem continuous_compact_oriented_integral_singleLinkHeatBathIndependentPairKernel_sqDiff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    (∫ y : C.base.Configuration × C.base.Configuration,
        (O y.1 - O y.2) ^ 2
        ∂C.singleLinkHeatBathIndependentPairKernel target A) =
      C.singleLinkConditionalIndependentPairDifferenceEnergyBCF
        target O A := by
  have hO : StronglyMeasurable
      (fun B : C.base.Configuration => O B) :=
    O.continuous.stronglyMeasurable
  have hSq : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (O y.1 - O y.2) ^ 2) := by
    have hDiff :=
      (hO.comp_measurable measurable_fst).sub
        (hO.comp_measurable measurable_snd)
    simpa [pow_two] using hDiff.mul hDiff
  rw [continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_apply]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalIndependentPairDifferenceEnergyBCF
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalPairConfigurationMap]
    using
      (MeasureTheory.integral_map
        (continuous_compact_oriented_singleLinkConditionalPairConfigurationMap_continuous
          C A target).measurable.aemeasurable
        hSq.aestronglyMeasurable)

/-- Mapping the first component of the native pair kernel recovers the exact
one-link heat-bath kernel. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_map_fst
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathIndependentPairKernel target).map Prod.fst =
      C.singleLinkHeatBathKernel target := by
  ext A : 1
  rw [Kernel.map_apply _ measurable_fst A]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairKernel
  rw [Kernel.prod_apply, Measure.map_fst_prod, measure_univ, one_smul]

/-- Mapping the second component of the native pair kernel also recovers the
exact one-link heat-bath kernel. -/
theorem continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_map_snd
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathIndependentPairKernel target).map Prod.snd =
      C.singleLinkHeatBathKernel target := by
  ext A : 1
  rw [Kernel.map_apply _ measurable_snd A]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairKernel
  rw [Kernel.prod_apply, Measure.map_snd_prod, measure_univ, one_smul]

/-- Gibbs-average the native conditional-pair kernel to obtain the canonical
reference law on configuration pairs. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.base.Configuration × C.base.Configuration) :=
  C.singleLinkHeatBathIndependentPairKernel target ∘ₘ C.gibbsMeasure

/-- The Gibbs-averaged native conditional-pair reference law is a probability
measure. -/
instance continuousCompactOriented_singleLinkHeatBathIndependentPairMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.singleLinkHeatBathIndependentPairMeasure target) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure
  infer_instance

/-- The first marginal of the native conditional-pair reference law is the
Gibbs measure. -/
theorem continuous_compact_oriented_map_fst_singleLinkHeatBathIndependentPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.singleLinkHeatBathIndependentPairMeasure target) =
      C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure
  rw [Measure.map_comp C.gibbsMeasure
    (C.singleLinkHeatBathIndependentPairKernel target) measurable_fst,
    continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_map_fst,
    continuous_compact_oriented_singleLinkHeatBathKernel_stationary]

/-- The second marginal of the native conditional-pair reference law is also
the Gibbs measure. -/
theorem continuous_compact_oriented_map_snd_singleLinkHeatBathIndependentPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.singleLinkHeatBathIndependentPairMeasure target) =
      C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathIndependentPairMeasure
  rw [Measure.map_comp C.gibbsMeasure
    (C.singleLinkHeatBathIndependentPairKernel target) measurable_snd,
    continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_map_snd,
    continuous_compact_oriented_singleLinkHeatBathKernel_stationary]

end

end MathlibAnalytic
end MGAP4D
