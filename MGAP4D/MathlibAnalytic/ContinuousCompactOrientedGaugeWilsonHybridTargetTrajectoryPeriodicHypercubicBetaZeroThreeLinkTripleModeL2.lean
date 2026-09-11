import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCenteredWilsonCoordinateTripleBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityThreeTripleModeEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The Gibbs `L²` representative of a three-coordinate centered product. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
      target source third)

/-- The three-link triple mode is nonzero for pairwise distinct coordinates. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_ne_zero
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        target source third ≠ 0 := by
  intro hZero
  have hToLp :
      BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
            target source third) =
        BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
            target source third) =
        0 at hZero
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
      using hZero
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third = 0 :=
    (BoundedContinuousFunction.toLp_injective
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hToLp
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_ne_zero
      target source third hTargetSource hTargetThird hSourceThird hBCF

/-- A zero BCF coordinate average makes the corresponding fluctuation
projection fix the triple mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_self_of_projection_eq_zero
    (target source third edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hBCFProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
            target source third) =
        fun _ => 0) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        target source third := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
            target source third) = 0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
              target source third)) = 0
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
              target source third) = 0 := by
      ext A
      exact congrFun hBCFProjection A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjection, sub_zero]

/-- A fixed BCF coordinate average makes the corresponding fluctuation
projection annihilate the triple mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_zero_of_projection_eq_self
    (target source third edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hBCFProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
            target source third) =
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
            target source third) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
              target source third)) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
            target source third)
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
              target source third) =
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
            target source third := by
      ext A
      exact congrFun hBCFProjection A
    rw [hBCF]
  rw [hProjection, sub_self]

/-- The first selected fluctuation projection fixes the triple mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_target_fluctuation_eq_self
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        target
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        target source third := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_self_of_projection_eq_zero
      target source third target
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_target_eq_zero
        target source third hTargetSource hTargetThird)

/-- The second selected fluctuation projection fixes the triple mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_source_fluctuation_eq_self
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        target source third := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_self_of_projection_eq_zero
      target source third source
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_source_eq_zero
        target source third hTargetSource hSourceThird)

/-- The third selected fluctuation projection fixes the triple mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_third_fluctuation_eq_self
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        third
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        target source third := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_self_of_projection_eq_zero
      target source third third
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_third_eq_zero
        target source third hTargetThird hSourceThird)

/-- Every unselected fluctuation projection annihilates the triple mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_zero_of_ne
    (target source third edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source)
    (hThird : edge ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third) = 0 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_zero_of_projection_eq_self
      target source third edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_eq_self_of_ne
        target source third edge hTarget hSource hThird)

/-- Every pairwise-distinct triple mode belongs to its three-coordinate joint
sector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_threeLinkTripleModeL2_mem_triple_fluctuationJointSector
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        target source third ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {target, source, third} := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases : edge = target ∨ edge = source ∨ edge = third := by
      simpa using hEdge
    rcases hCases with hEq | hEq | hEq
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_target_fluctuation_eq_self
          target source third hTargetSource hTargetThird
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_source_fluctuation_eq_self
          target source third hTargetSource hSourceThird
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_third_fluctuation_eq_self
          target source third hTargetThird hSourceThird
  · intro edge hEdge
    apply
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2_fluctuation_eq_zero_of_ne
        target source third edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- The actual cardinality-three projector fixes every pairwise-distinct
three-link triple mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_three_apply_threeLinkTripleMode_eq
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        3
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
          target source third) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeLinkTripleModeL2
        target source third := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
      3 {target, source, third}
      (finset_triple_card_eq_three
        target source third hTargetSource hTargetThird hSourceThird)
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_threeLinkTripleModeL2_mem_triple_fluctuationJointSector
        target source third hTargetSource hTargetThird hSourceThird)

end

end MathlibAnalytic
end MGAP4D
