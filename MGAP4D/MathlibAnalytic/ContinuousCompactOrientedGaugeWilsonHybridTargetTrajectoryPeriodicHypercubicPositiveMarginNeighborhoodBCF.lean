import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicEndpointMarginWitnessBCF
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The rank-zero insertion profile is jointly continuous in the original
configuration pair and the inserted Gauge value. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF_joint_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (fun p : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
          target O p.1 p.2) := by
  have h : Continuous
      (fun p : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        O (C.base.replaceLink p.1.1 target p.2)) :=
    O.continuous.comp
      ((continuous_compact_oriented_replaceLink_uncurry C target).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF]
    using h

/-- The full-rank insertion profile is jointly continuous in the original
configuration pair and the inserted Gauge value. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF_joint_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (fun p : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
          target O p.1 p.2) := by
  have h : Continuous
      (fun p : (C.base.Configuration × C.base.Configuration) × C.base.Gauge =>
        O (C.base.replaceLink p.1.2 target p.2)) :=
    O.continuous.comp
      ((continuous_compact_oriented_replaceLink_uncurry C target).comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF]
    using h

/-- The rank-zero insertion-profile oscillation varies continuously with the
original configuration pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF
        target O) := by
  let f : (C.base.Configuration × C.base.Configuration) → C.base.Gauge → ℝ :=
    fun z g =>
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
        target O z g
  have hf : Continuous ↿f := by
    simpa [f] using
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF_joint_continuous
        C target O)
  have hSup : Continuous
      (fun z => sSup (f z '' (Set.univ : Set C.base.Gauge))) :=
    isCompact_univ.continuous_sSup hf
  have hInf : Continuous
      (fun z => sInf (f z '' (Set.univ : Set C.base.Gauge))) :=
    isCompact_univ.continuous_sInf hf
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF,
      f, Set.image_univ]
    using hSup.sub hInf

/-- The full-rank insertion-profile oscillation varies continuously with the
original configuration pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF
        target O) := by
  let f : (C.base.Configuration × C.base.Configuration) → C.base.Gauge → ℝ :=
    fun z g =>
      C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
        target O z g
  have hf : Continuous ↿f := by
    simpa [f] using
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF_joint_continuous
        C target O)
  have hSup : Continuous
      (fun z => sSup (f z '' (Set.univ : Set C.base.Gauge))) :=
    isCompact_univ.continuous_sSup hf
  have hInf : Continuous
      (fun z => sInf (f z '' (Set.univ : Set C.base.Gauge))) :=
    isCompact_univ.continuous_sInf hf
  simpa
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF,
      f, Set.image_univ]
    using hSup.sub hInf

/-- The absolute endpoint oscillation margin is continuous in the original
configuration pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target O) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
  exact
    ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileOscillationBCF_continuous
        C target O).sub
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileOscillationBCF_continuous
        C target O)).abs

/-- The set of original configuration pairs with positive endpoint oscillation
margin is open. -/
theorem continuous_compact_oriented_isOpen_endpointInsertionProfileOscillationMarginBCF_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    IsOpen
      {z : C.base.Configuration × C.base.Configuration |
        0 < C.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          target O z} := by
  exact isOpen_lt continuous_const
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_continuous
      C target O)

/-- The product normalized Haar law on finite physical-link configurations is
positive on every nonempty open configuration region. -/
instance continuousCompactOriented_configurationHaarMeasure_isOpenPosMeasureBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Measure.IsOpenPosMeasure C.base.configurationHaarMeasure := by
  unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
  infer_instance

/-- The normalized real density of the finite-volume Gibbs law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsDensityBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) : ℝ :=
  Real.exp (C.base.gibbsExponent A) / C.base.partitionFunction

/-- The finite-volume Gibbs density is pointwise strictly positive. -/
theorem continuous_compact_oriented_gibbsDensityBCF_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration) :
    0 < C.gibbsDensityBCF A := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsDensityBCF
  exact div_pos (Real.exp_pos _)
    (compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C))

/-- The finite-volume Gibbs density is continuous. -/
theorem continuous_compact_oriented_gibbsDensityBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Continuous C.gibbsDensityBCF := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsDensityBCF
  exact (continuous_compact_oriented_boltzmannFactor C).div_const _

/-- Density representation of the canonical finite-volume Gibbs law. -/
theorem continuous_compact_oriented_gibbsMeasure_eq_withDensityBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.gibbsMeasure =
      C.base.configurationHaarMeasure.withDensity
        (fun A => ENNReal.ofReal (C.gibbsDensityBCF A)) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [compact_oriented_gibbsMeasure_eq_withDensity]
  rfl

/-- Every canonical finite-volume Gibbs law is positive on every nonempty open
configuration region. -/
instance continuousCompactOriented_gibbsMeasure_isOpenPosMeasureBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Measure.IsOpenPosMeasure C.gibbsMeasure := by
  rw [continuous_compact_oriented_gibbsMeasure_eq_withDensityBCF]
  let μ : Measure C.base.Configuration := C.base.configurationHaarMeasure
  let f : C.base.Configuration → ℝ≥0∞ := fun A =>
    ENNReal.ofReal (C.gibbsDensityBCF A)
  change Measure.IsOpenPosMeasure (μ.withDensity f)
  have hf : Measurable f :=
    (continuous_compact_oriented_gibbsDensityBCF_continuous C).measurable.ennreal_ofReal
  refine ⟨?_⟩
  intro U hU hUne
  intro hZero
  have hBase : μ ({A | f A ≠ 0} ∩ U) = 0 :=
    (withDensity_apply_eq_zero (μ := μ) hf).1 hZero
  have hEverywhere : {A | f A ≠ 0} = Set.univ := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ne_of_gt
      (ENNReal.ofReal_pos.2
        (continuous_compact_oriented_gibbsDensityBCF_pos C A))
  rw [hEverywhere, Set.univ_inter] at hBase
  exact hU.measure_ne_zero μ hUne hBase

/-- The independent Gibbs-pair law is positive on every nonempty open pair
region. -/
instance continuousCompactOriented_gibbsMeasure_prod_isOpenPosMeasureBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Measure.IsOpenPosMeasure (C.gibbsMeasure.prod C.gibbsMeasure) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  infer_instance

/-- The actual periodic positive-margin neighborhood around the concrete pair
constructed in the previous theorem unit. -/
def periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF :
    Set
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :=
  {z |
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z}

/-- The actual periodic positive-margin neighborhood is open. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF_isOpen :
    IsOpen periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF := by
  exact
    continuous_compact_oriented_isOpen_endpointInsertionProfileOscillationMarginBCF_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF

/-- The concrete identity/far-side-center endpoint pair lies in the actual
positive-margin neighborhood. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_mem_positiveMarginNeighborhoodBCF :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ∈
      periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF := by
  exact periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_pos

/-- The actual periodic positive-margin neighborhood has strictly positive
independent Gibbs-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF_measure_pos :
    0 <
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF := by
  letI : IsProbabilityMeasure
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  exact
    periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF_isOpen.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointPair,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_mem_positiveMarginNeighborhoodBCF⟩

/-- Consequently the actual six-plaquette observable has positive endpoint
margin on a non-null independent Gibbs-pair family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fiberwise_margin_pos :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
  simpa only [Filter.frequently_iff, ae_iff, Classical.not_not] using
    ne_of_gt
      periodicHypercubicThreeSpecialUnitaryTwoPositiveMarginNeighborhoodBCF_measure_pos

/-- The non-null actual positive-margin family forces a positive global endpoint
conditional-variance gap for the concrete six-plaquette observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_globalGap_pos :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF_implies_gap_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fiberwise_margin_pos

end

end MathlibAnalytic
end MGAP4D
