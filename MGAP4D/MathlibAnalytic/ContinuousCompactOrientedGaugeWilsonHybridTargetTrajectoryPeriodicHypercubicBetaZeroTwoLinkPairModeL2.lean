import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCenteredWilsonCoordinatePairBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityTwoPairModeEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The Gibbs `L²` representative of a two-coordinate centered product. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
      target source)

/-- The two-link pair mode is nonzero for distinct coordinates. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_ne_zero
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source ≠ 0 := by
  intro hZero
  have hToLp :
      BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            target source) =
        BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            target source) =
        0 at hZero
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
      using hZero
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source = 0 :=
    (BoundedContinuousFunction.toLp_injective
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hToLp
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_ne_zero
      target source hNe hBCF

/-- The first selected fluctuation projection fixes the pair mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_target_fluctuation_eq_self
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        target
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          target
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            target source) = 0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          target
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source)) = 0
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        target
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            target
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source) = 0 := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_target_eq_zero
          target source hNe) A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjection, sub_zero]

/-- The second selected fluctuation projection fixes the pair mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_source_fluctuation_eq_self
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          source
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            target source) = 0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          source
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source)) = 0
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        source
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            source
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source) = 0 := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_source_eq_zero
          target source hNe) A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjection, sub_zero]

/-- Every unselected fluctuation projection annihilates the pair mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_fluctuation_eq_zero_of_ne
    (target source edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
            target source) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source)) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            target source)
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
          target source)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
              target source) =
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            target source := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_projection_eq_self_of_ne
          target source edge hTarget hSource) A
    rw [hBCF]
  rw [hProjection, sub_self]

/-- Every distinct pair mode belongs to its two-coordinate joint sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoLinkPairModeL2_mem_pair_fluctuationJointSector
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {target, source} := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases : edge = target ∨ edge = source := by
      simpa using hEdge
    rcases hCases with hEq | hEq
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_target_fluctuation_eq_self
          target source hNe
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_source_fluctuation_eq_self
          target source hNe
  · intro edge hEdge
    apply
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2_fluctuation_eq_zero_of_ne
        target source edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- The actual cardinality-two projector fixes every distinct two-link pair
mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_two_apply_twoLinkPairMode_eq
    (target source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hNe : target ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
          target source) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoLinkPairModeL2
        target source := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
      2 {target, source}
      (finset_pair_card_eq_two target source hNe)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoLinkPairModeL2_mem_pair_fluctuationJointSector
        target source hNe)

end

end MathlibAnalytic
end MGAP4D
