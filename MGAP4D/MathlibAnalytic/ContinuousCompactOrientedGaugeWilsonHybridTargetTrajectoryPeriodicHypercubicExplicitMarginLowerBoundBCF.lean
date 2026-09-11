import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicPositiveMarginNeighborhoodBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set Filter
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

local instance periodicExplicitMarginLowerBoundEndpointSystemT2Space :
    T2Space periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge := by
  change T2Space (SpecialUnitaryMatrixGroup 2)
  infer_instance

/-- The explicit side-three periodic `SU(2)` endpoint-margin neighborhood at
threshold six.  The concrete endpoint margin is exactly twelve, so this leaves
an explicit factor-two margin reserve. -/
def periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF :
    Set
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :=
  {z |
    6 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z}

/-- The explicit threshold-six endpoint-margin neighborhood is open. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_isOpen :
    IsOpen periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  exact isOpen_lt continuous_const
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF_continuous
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF)

/-- The concrete identity/far-side-center pair belongs to the explicit
threshold-six neighborhood because its exact endpoint margin is twelve. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_mem_explicitMarginLowerBoundNeighborhoodBCF :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointPair ∈
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  change
    (6 : ℝ) <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
        periodicHypercubicThreeSpecialUnitaryTwoEndpointPair
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_margin_eq_twelve]
  norm_num

/-- Hence the explicit threshold-six endpoint-margin neighborhood is nonempty. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_nonempty :
    periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF.Nonempty := by
  exact
    ⟨periodicHypercubicThreeSpecialUnitaryTwoEndpointPair,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointPair_mem_explicitMarginLowerBoundNeighborhoodBCF⟩

/-- The explicit threshold-six neighborhood has strictly positive independent
finite-volume Gibbs-pair mass. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_measure_pos :
    0 <
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF := by
  letI : IsProbabilityMeasure
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  exact
    periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_isOpen.measure_pos
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_nonempty

/-- Every pair in the explicit neighborhood has endpoint oscillation margin
strictly larger than six. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_margin_gt_six
    {z :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration}
    (hz : z ∈ periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF) :
    (6 : ℝ) <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
  exact hz

/-- In particular, every pair in the explicit neighborhood has the uniform
weak endpoint-margin lower bound six. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_margin_ge_six
    {z :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ×
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration}
    (hz : z ∈ periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF) :
    (6 : ℝ) ≤
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
  exact le_of_lt
    (periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_margin_gt_six hz)

/-- The strict threshold-six margin inequality holds on a non-null independent
Gibbs-pair family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_frequently_margin_gt_six :
    ∃ᵐ z ∂(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
      (6 : ℝ) <
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          periodicHypercubicThreeOriginAxisZeroTarget
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
  rw [frequently_ae_iff]
  simpa only [periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF]
    using
      ne_of_gt
        periodicHypercubicThreeSpecialUnitaryTwoExplicitMarginLowerBoundNeighborhoodBCF_measure_pos

/-- The weak threshold-six margin inequality holds on a non-null independent
Gibbs-pair family. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_frequently_margin_ge_six :
    ∃ᵐ z ∂(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
      (6 : ℝ) ≤
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
          periodicHypercubicThreeOriginAxisZeroTarget
          periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_frequently_margin_gt_six.mono
      fun _ hz => le_of_lt hz

/-- The actual periodic six-plaquette observable satisfies the generic
finite-volume lower-bound predicate with the explicit witness `δ = 6`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fiberwise_margin_lowerBound_six :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  refine ⟨6, by norm_num, ?_⟩
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_frequently_margin_ge_six

/-- An explicit existential receipt records that the lower-bound witness is
exactly six, rather than merely some unspecified positive real number. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_exists_explicit_margin_lowerBound_six :
    ∃ δ : ℝ,
      δ = 6 ∧
      0 < δ ∧
      ∃ᵐ z ∂(periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure.prod
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
        δ ≤
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
            periodicHypercubicThreeOriginAxisZeroTarget
            periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF z := by
  refine ⟨6, rfl, by norm_num, ?_⟩
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_frequently_margin_ge_six

/-- The explicit threshold-six lower bound recovers positive endpoint margin on
a non-null independent Gibbs-pair family through the generic lower-bound API. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fiberwise_margin_pos_of_lowerBound_six :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginPosBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_margin_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fiberwise_margin_lowerBound_six

/-- The explicit threshold-six lower-bound witness forces a positive actual
finite-volume global endpoint conditional-variance gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_globalGap_pos_of_lowerBound_six :
    0 < periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileOscillationMarginLowerBoundBCF_implies_gap_pos
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF
      periodicHypercubicThreeSpecialUnitaryTwoEndpointObservableBCF_fiberwise_margin_lowerBound_six

end

end MathlibAnalytic
end MGAP4D
