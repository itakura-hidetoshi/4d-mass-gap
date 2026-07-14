import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridEndpointCouplingBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The canonical pre/post endpoint pair of one independent Gibbs-pair hybrid
step. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.base.Configuration × C.base.Configuration →
      C.base.Configuration × C.base.Configuration :=
  fun z =>
    (C.independentPairHybridPreEndpointMap target z,
      C.independentPairHybridPostEndpointMap target z)

/-- The canonical endpoint-pair map is continuous. -/
theorem continuous_compact_oriented_independentPairHybridEndpointPairMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (C.independentPairHybridEndpointPairMap target) := by
  exact
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_continuous
      C target).prodMk
      (continuous_compact_oriented_independentPairHybridPostEndpointMap_continuous
        C target)

/-- The canonical endpoint-pair map is measurable. -/
theorem continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measurable (C.independentPairHybridEndpointPairMap target) :=
  (continuous_compact_oriented_independentPairHybridEndpointPairMap_continuous
    C target).measurable

/-- Actual transport plan coupling the pre-step and post-step hybrid endpoint
laws. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.base.Configuration × C.base.Configuration) :=
  Measure.map (C.independentPairHybridEndpointPairMap target)
    (C.gibbsMeasure.prod C.gibbsMeasure)

/-- Integrate a strongly measurable real observable against the canonical
endpoint transport plan. -/
theorem continuous_compact_oriented_integral_independentPairHybridEndpointPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration × C.base.Configuration → ℝ)
    (hf : StronglyMeasurable f) :
    (∫ y, f y ∂C.independentPairHybridEndpointPairMeasure target) =
      ∫ z, f (C.independentPairHybridEndpointPairMap target z)
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
  exact MeasureTheory.integral_map
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target).aemeasurable
    hf.aestronglyMeasurable

/-- Build a pre/post configuration pair from the pre-endpoint/right-target
coupling carrier. -/
theorem continuous_compact_oriented_hybridEndpointPairFromCoupling_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun x : C.base.Configuration × C.base.Gauge =>
        (x.1, C.base.replaceLink x.1 target x.2)) := by
  exact
    (continuous_fst : Continuous
      (fun x : C.base.Configuration × C.base.Gauge => x.1)).prodMk
      (continuous_compact_oriented_replaceLink_prod_hybridEndpoint C target)

/-- The configuration-pair transport plan factors through the explicit
pre-endpoint/right-target coupling from the preceding layer. -/
theorem continuous_compact_oriented_independentPairHybridEndpointPairMeasure_eq_map_endpointCoupling
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridEndpointPairMeasure target =
      Measure.map
        (fun x : C.base.Configuration × C.base.Gauge =>
          (x.1, C.base.replaceLink x.1 target x.2))
        (C.independentPairHybridPreEndpointRightTargetMeasure target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointRightTargetMeasure
  rw [Measure.map_map
    (continuous_compact_oriented_hybridEndpointPairFromCoupling_continuous
      C target).measurable
    (continuous_compact_oriented_independentPairHybridPreEndpointRightTargetMap_continuous
      C target).measurable]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z => by
    apply Prod.ext
    · rfl
    · exact
        continuous_compact_oriented_independentPairHybridPostEndpointMap_eq_replaceLink_pre_rightTarget
          C target z

/-- The first marginal of the endpoint transport plan is exactly the pre-step
endpoint law. -/
theorem continuous_compact_oriented_map_fst_independentPairHybridEndpointPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.independentPairHybridEndpointPairMeasure target) =
      C.independentPairHybridPreEndpointMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
  rw [Measure.map_map measurable_fst
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The second marginal of the endpoint transport plan is exactly the post-step
endpoint law. -/
theorem continuous_compact_oriented_map_snd_independentPairHybridEndpointPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.independentPairHybridEndpointPairMeasure target) =
      C.independentPairHybridPostEndpointMeasure target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMeasure
  rw [Measure.map_map measurable_snd
    (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
      C target)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Every pair generated by the endpoint transport plan agrees away from the
updated physical link. -/
theorem continuous_compact_oriented_independentPairHybridEndpointPairMap_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.base.AgreeOffLink
      (C.independentPairHybridEndpointPairMap target z).2
      (C.independentPairHybridEndpointPairMap target z).1
      target := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap]
    using
      continuous_compact_oriented_independentPairHybridConfiguration_rank_agreeOffLink
        C z.1 z.2 target

/-- Before the target hybrid step, the target coordinate is still the left Gibbs
endpoint value. -/
@[simp]
theorem continuous_compact_oriented_independentPairHybridPreEndpointMap_apply_target
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridPreEndpointMap target z target = z.1 target := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridConfiguration]
    using
      FiniteHybridPath.configuration_rank_apply
        C.canonicalEdgeOrder z.1 z.2 target

/-- After the target hybrid step, the target coordinate is the right Gibbs
endpoint value. -/
@[simp]
theorem continuous_compact_oriented_independentPairHybridPostEndpointMap_apply_target
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridPostEndpointMap target z target = z.2 target := by
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridConfiguration]
    using
      FiniteHybridPath.configuration_rank_succ_apply
        C.canonicalEdgeOrder z.1 z.2 target

/-- Gibbs marginal law of one physical target coordinate. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsTargetCoordinateMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  Measure.map (fun A : C.base.Configuration => A target) C.gibbsMeasure

/-- The target-coordinate marginal of the pre-step endpoint law is the genuine
Gibbs target-coordinate marginal. -/
theorem continuous_compact_oriented_map_apply_target_independentPairHybridPreEndpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map (fun A : C.base.Configuration => A target)
        (C.independentPairHybridPreEndpointMeasure target) =
      C.gibbsTargetCoordinateMeasure target := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsTargetCoordinateMeasure
  rw [Measure.map_map (continuous_apply target).measurable
    (continuous_compact_oriented_independentPairHybridPreEndpointMap_measurable
      C target)]
  calc
    Measure.map
        ((fun A : C.base.Configuration => A target) ∘
          C.independentPairHybridPreEndpointMap target)
        (C.gibbsMeasure.prod C.gibbsMeasure) =
      Measure.map
        ((fun A : C.base.Configuration => A target) ∘ Prod.fst)
        (C.gibbsMeasure.prod C.gibbsMeasure) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun z => by
        simp
    _ = Measure.map (fun A : C.base.Configuration => A target)
        (Measure.map Prod.fst (C.gibbsMeasure.prod C.gibbsMeasure)) := by
      rw [Measure.map_map (continuous_apply target).measurable measurable_fst]
    _ = Measure.map (fun A : C.base.Configuration => A target)
        C.gibbsMeasure := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The target-coordinate marginal of the post-step endpoint law is also the
genuine Gibbs target-coordinate marginal. -/
theorem continuous_compact_oriented_map_apply_target_independentPairHybridPostEndpointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map (fun A : C.base.Configuration => A target)
        (C.independentPairHybridPostEndpointMeasure target) =
      C.gibbsTargetCoordinateMeasure target := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsTargetCoordinateMeasure
  rw [Measure.map_map (continuous_apply target).measurable
    (continuous_compact_oriented_independentPairHybridPostEndpointMap_measurable
      C target)]
  calc
    Measure.map
        ((fun A : C.base.Configuration => A target) ∘
          C.independentPairHybridPostEndpointMap target)
        (C.gibbsMeasure.prod C.gibbsMeasure) =
      Measure.map
        ((fun A : C.base.Configuration => A target) ∘ Prod.snd)
        (C.gibbsMeasure.prod C.gibbsMeasure) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun z => by
        simp
    _ = Measure.map (fun A : C.base.Configuration => A target)
        (Measure.map Prod.snd (C.gibbsMeasure.prod C.gibbsMeasure)) := by
      rw [Measure.map_map (continuous_apply target).measurable measurable_snd]
    _ = Measure.map (fun A : C.base.Configuration => A target)
        C.gibbsMeasure := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The canonical hybrid increment energy is exactly the squared difference of
native heat-bath fluctuations under the endpoint transport coupling. -/
theorem continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_eq_endpointPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridIncrementEnergyBCF target O =
      ∫ y : C.base.Configuration × C.base.Configuration,
        (C.singleLinkHeatBathFluctuation target O y.2 -
          C.singleLinkHeatBathFluctuation target O y.1) ^ 2
        ∂C.independentPairHybridEndpointPairMeasure target := by
  have hFluctuation :=
    continuous_compact_oriented_singleLinkHeatBathFluctuation_stronglyMeasurable
      C target O O.continuous.stronglyMeasurable
  have hPost : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        C.singleLinkHeatBathFluctuation target O y.2) :=
    hFluctuation.comp_measurable measurable_snd
  have hPre : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        C.singleLinkHeatBathFluctuation target O y.1) :=
    hFluctuation.comp_measurable measurable_fst
  have hSquare : StronglyMeasurable
      (fun y : C.base.Configuration × C.base.Configuration =>
        (C.singleLinkHeatBathFluctuation target O y.2 -
          C.singleLinkHeatBathFluctuation target O y.1) ^ 2) := by
    have hDiff := hPost.sub hPre
    simpa [pow_two] using hDiff.mul hDiff
  symm
  rw [continuous_compact_oriented_integral_independentPairHybridEndpointPairMeasure
    C target _ hSquare]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementEnergyBCF
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp
      [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap]
    exact congrArg (fun x : ℝ => x ^ 2)
      (continuous_compact_oriented_independentPairHybridIncrementBCF_eq_fluctuation_sub
        C target O z.1 z.2).symm

end

end MathlibAnalytic
end MGAP4D
