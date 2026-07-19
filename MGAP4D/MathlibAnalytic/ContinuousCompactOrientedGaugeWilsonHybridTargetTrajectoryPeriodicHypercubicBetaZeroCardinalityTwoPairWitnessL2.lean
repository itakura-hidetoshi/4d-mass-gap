import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroTwoLinkPairModeL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityTwoReceiptEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- There exists a second physical edge distinct from the distinguished edge. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_ne_originAxisZeroTarget :
    ∃ source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      source ≠ periodicHypercubicThreeOriginAxisZeroTarget := by
  letI : Nontrivial
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
      norm_num)
  exact exists_ne periodicHypercubicThreeOriginAxisZeroTarget

/-- A canonical noncomputably selected second physical edge. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.choose
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_ne_originAxisZeroTarget

theorem periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne :
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ≠
      periodicHypercubicThreeOriginAxisZeroTarget :=
  Classical.choose_spec
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exists_edge_ne_originAxisZeroTarget

/-- The actual cardinality-two projector is nonzero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      2 ≠ 0 := by
  let source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
  have hNe :
      periodicHypercubicThreeOriginAxisZeroTarget ≠ source :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
  intro hZero
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          periodicHypercubicThreeOriginAxisZeroTarget source))
    hZero
  have hProjectedZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            periodicHypercubicThreeOriginAxisZeroTarget source) = 0 := by
    simpa using hApply
  have hProjectedSelf :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_apply_twoLinkPairMode_eq
      periodicHypercubicThreeOriginAxisZeroTarget source hNe
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_ne_zero
      periodicHypercubicThreeOriginAxisZeroTarget source hNe
      (hProjectedSelf.symm.trans hProjectedZero)

/-- The actual cardinality-two joint-sector sum is non-bottom. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_two_ne_bot :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      2 ≠ ⊥ := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_ne_zero_iff_cardinalityJointSectorSumSubmoduleL2_ne_bot
      2).1
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero

/-- The nonzero cardinality-two projector realizes eigenvalue two through the
cardinality-sector criterion. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_two_mem_heatBathPointSpectrumL2_of_cardinalityTwoProjector :
    (2 : ℝ) ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 := by
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_natCast_mem_heatBathPointSpectrumL2_of_fluctuationCardinalityProjectorL2_ne_zero
      2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero

/-- Compact receipt for the actual beta-zero cardinality-two pair witness. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityTwoPairWitnessL2Receipt :
    Prop :=
  periodicHypercubicThreeOriginAxisZeroTarget ≠
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
      {periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget} ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      2
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      2 ≠ 0 ∧
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
      2 ≠ ⊥ ∧
  (2 : ℝ) ∈
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2

/-- The actual beta-zero cardinality-two pair-witness receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityTwoPairWitnessL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityTwoPairWitnessL2Receipt := by
  have hNe :
      periodicHypercubicThreeOriginAxisZeroTarget ≠
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget :=
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm
  exact ⟨
    hNe,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_ne_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget hNe,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoLinkPairModeL2_mem_pair_fluctuationJointSector
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget hNe,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_apply_twoLinkPairMode_eq
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget hNe,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_ne_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_two_ne_bot,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_two_mem_heatBathPointSpectrumL2_of_cardinalityTwoProjector⟩

end

end MathlibAnalytic
end MGAP4D
