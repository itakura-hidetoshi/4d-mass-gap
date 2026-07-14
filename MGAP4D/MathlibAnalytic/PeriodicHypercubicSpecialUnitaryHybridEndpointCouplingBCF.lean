import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridEndpointPushforwardBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The pre-step hybrid endpoint together with the target-link value supplied by
its independent right Gibbs endpoint. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointRightTargetMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration →
      C.base.Configuration × C.base.Gauge :=
  fun z => (C.independentPairHybridPreEndpointMap target z, z.2 target)

/-- The pre-endpoint/right-target coupling map is continuous. -/
theorem continuous_compact_oriented_independentPairHybridPreEndpointRightTargetMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.independentPairHybridPreEndpointRightTargetMap target) := by
  exact
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_continuous
      C target).prod
      ((continuous_apply target).comp continuous_snd)

/-- Joint physical-link replacement is continuous in both the background
configuration and the inserted compact-group value. -/
theorem continuous_compact_oriented_replaceLink_prod_hybridEndpoint
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        C.base.replaceLink z.1 target z.2) := by
  classical
  apply continuous_pi
  intro source
  by_cases hSource : source = target
  · subst source
    simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
      (continuous_snd : Continuous
        (fun z : C.base.Configuration × C.base.Gauge => z.2))
  · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, hSource] using
      ((continuous_apply source).comp
        (continuous_fst : Continuous
          (fun z : C.base.Configuration × C.base.Gauge => z.1)))

/-- Pointwise, the post-step endpoint is obtained from the pre-step endpoint by
inserting the target-link value of the independent right Gibbs configuration. -/
theorem continuous_compact_oriented_independentPairHybridPostEndpointMap_eq_replaceLink_pre_rightTarget
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridPostEndpointMap target z =
      C.base.replaceLink
        (C.independentPairHybridPreEndpointMap target z)
        target (z.2 target) := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap]
    using
      continuous_compact_oriented_independentPairHybridConfiguration_rank_succ_eq_replaceLink
        C z.1 z.2 target

/-- Joint law of the pre-step endpoint and the right Gibbs target-link value.
This is an actual coupling law; it does not assert independence between these two
components. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointRightTargetMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.base.Configuration × C.base.Gauge) :=
  Measure.map (C.independentPairHybridPreEndpointRightTargetMap target)
    (C.gibbsMeasure.prod C.gibbsMeasure)

/-- Integrate a strongly measurable observable against the explicit
pre-endpoint/right-target coupling law. -/
theorem continuous_compact_oriented_integral_independentPairHybridPreEndpointRightTargetMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration × C.base.Gauge → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ x, f x ∂C.independentPairHybridPreEndpointRightTargetMeasure target) =
      ∫ z, f (C.independentPairHybridPreEndpointRightTargetMap target z)
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointRightTargetMeasure
  exact MeasureTheory.integral_map
    (continuous_compact_oriented_independentPairHybridPreEndpointRightTargetMap_continuous
      C target).measurable.aemeasurable
    hf.aestronglyMeasurable

/-- The post-step endpoint law is exactly the single-link replacement pushforward
of the explicit pre-endpoint/right-target coupling law. -/
theorem continuous_compact_oriented_independentPairHybridPostEndpointMeasure_eq_replaceLink_map_coupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridPostEndpointMeasure target =
      Measure.map
        (fun x : C.base.Configuration × C.base.Gauge =>
          C.base.replaceLink x.1 target x.2)
        (C.independentPairHybridPreEndpointRightTargetMeasure target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointRightTargetMeasure
  rw [Measure.map_map
    (continuous_compact_oriented_replaceLink_prod_hybridEndpoint
      C target).measurable
    (continuous_compact_oriented_independentPairHybridPreEndpointRightTargetMap_continuous
      C target).measurable]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z =>
    continuous_compact_oriented_independentPairHybridPostEndpointMap_eq_replaceLink_pre_rightTarget
      C target z

/-- Exact integral transport from the post-step endpoint law to the common
pre-endpoint/right-target coupling carrier. -/
theorem continuous_compact_oriented_integral_independentPairHybridPostEndpointMeasure_eq_coupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ A, f A ∂C.independentPairHybridPostEndpointMeasure target) =
      ∫ x, f (C.base.replaceLink x.1 target x.2)
        ∂C.independentPairHybridPreEndpointRightTargetMeasure target := by
  rw [continuous_compact_oriented_independentPairHybridPostEndpointMeasure_eq_replaceLink_map_coupling]
  exact MeasureTheory.integral_map
    (continuous_compact_oriented_replaceLink_prod_hybridEndpoint
      C target).measurable.aemeasurable
    hf.aestronglyMeasurable

/-- The canonical hybrid increment energy is an exact fluctuation-difference
energy on the explicit pre-endpoint/right-target coupling carrier. -/
theorem continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_eq_endpointCoupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridIncrementEnergyBCF target O =
      ∫ x : C.base.Configuration × C.base.Gauge,
        (C.singleLinkHeatBathFluctuation target O
            (C.base.replaceLink x.1 target x.2) -
          C.singleLinkHeatBathFluctuation target O x.1) ^ 2
        ∂C.independentPairHybridPreEndpointRightTargetMeasure target := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  have hPost : StronglyMeasurable
      (fun x : C.base.Configuration × C.base.Gauge =>
        C.singleLinkHeatBathFluctuation target O
          (C.base.replaceLink x.1 target x.2)) :=
    hFluctuation.comp_measurable
      (continuous_compact_oriented_replaceLink_prod_hybridEndpoint
        C target).measurable
  have hPre : StronglyMeasurable
      (fun x : C.base.Configuration × C.base.Gauge =>
        C.singleLinkHeatBathFluctuation target O x.1) :=
    hFluctuation.comp_measurable measurable_fst
  have hSquare : StronglyMeasurable
      (fun x : C.base.Configuration × C.base.Gauge =>
        (C.singleLinkHeatBathFluctuation target O
            (C.base.replaceLink x.1 target x.2) -
          C.singleLinkHeatBathFluctuation target O x.1) ^ 2) := by
    have hDiff := hPost.sub hPre
    simpa [pow_two] using hDiff.mul hDiff
  symm
  rw [continuous_compact_oriented_integral_independentPairHybridPreEndpointRightTargetMeasure
    C target _ hSquare]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementEnergyBCF
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp
      [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointRightTargetMap]
    rw [← continuous_compact_oriented_independentPairHybridPostEndpointMap_eq_replaceLink_pre_rightTarget
      C target z]
    exact congrArg (fun x : ℝ => x ^ 2)
      (continuous_compact_oriented_independentPairHybridIncrementBCF_eq_fluctuation_sub
        C target O z.1 z.2).symm

end

end MathlibAnalytic
end MGAP4D
