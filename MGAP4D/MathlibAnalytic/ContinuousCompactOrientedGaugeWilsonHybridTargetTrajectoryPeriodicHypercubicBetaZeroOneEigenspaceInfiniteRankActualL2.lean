import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroOneEigenspaceInfiniteRankCompletionL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The injective linear passage from bounded-continuous observables to the
    actual Gibbs `L²` space, dedicated to the eigenvalue-one rank witness. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure where
  toFun F :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF F
  map_add' F G := by
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  map_smul' a F := by
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]

/-- The bounded-continuous to Gibbs-`L²` linear map is injective. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap_injective :
    Function.Injective
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap := by
  intro F G hFG
  change
    BoundedContinuousFunction.toLp
        2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure ℝ F =
      BoundedContinuousFunction.toLp
        2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure ℝ G at hFG
  exact
    (BoundedContinuousFunction.toLp_injective
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) hFG

/-- The countable actual Gibbs-`L²` family obtained from the centered positive
    Wilson-energy powers. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2
    (n : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
      n)

/-- The actual countable Gibbs-`L²` one-link power-fluctuation family is linearly
    independent. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2 := by
  have hMapped :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF_linearIndependent.map'
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap
      (LinearMap.ker_eq_bot.mpr
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap_injective)
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap]
    using hMapped

/-- The `L²` family is exactly the target-link fluctuation of the corresponding
    uncentered positive-power representative. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_eq_target_fluctuation
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2 n =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)) := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]

/-- The distinguished fluctuation projection fixes every member of the countable
    power family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_target_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2
          n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2
        n := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_eq_target_fluctuation]
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply_fluctuation
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget _

/-- Every other one-link fluctuation annihilates the uncentered target-coordinate
    positive-power representative. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        source
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n) := by
    intro A B hAgree
    simp only [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF,
      BoundedContinuousFunction.coe_pow]
    congr 1
    exact hAgree periodicHypercubicThreeOriginAxisZeroTarget (Ne.symm hSource)
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          source
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n := by
    ext A
    exact congrFun
      (continuous_compact_oriented_singleLinkHeatBathProjection_fixes
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        source
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n)
        hFiber) A
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  rw [hBCF, sub_self]

/-- Every non-target fluctuation projection annihilates every member of the
    countable target-link power family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (source :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hSource : source ≠ periodicHypercubicThreeOriginAxisZeroTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        source
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2
          n) = 0 := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_eq_target_fluctuation]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
      source periodicHypercubicThreeOriginAxisZeroTarget]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerL2_fluctuation_eq_zero_of_ne
      n source hSource]
  simp

/-- Every member of the countable family lies in the exact singleton joint
    sector at the distinguished physical link. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneInfiniteRankOneLinkPowerFluctuationL2_mem_singleton_fluctuationJointSector
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2
        n ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {periodicHypercubicThreeOriginAxisZeroTarget} := by
  exact
    continuousLinearMap_mem_singleton_jointSectorSubmoduleL2_of_eq_self_of_eq_zero_of_ne
      (Q := fun edge :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
            edge)
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_target_fluctuation_eq_self
        n)
      (fun source hSource =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_fluctuation_eq_zero_of_ne
          n source hSource)

/-- The actual beta-zero heat-bath eigenspace at eigenvalue one has Cardinal rank
    at least `aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          1) := by
  let Q := fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      edge
  have hGeneric :=
    continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
      (Q := Q)
      (s := {periodicHypercubicThreeOriginAxisZeroTarget})
      (v :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2)
      (fun edge f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge f)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_linearIndependent
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneInfiniteRankOneLinkPowerFluctuationL2_mem_singleton_fluctuationJointSector
  simpa [Q, Finset.card_singleton,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
    using hGeneric

/-- The range of the actual cardinality-one projector has rank at least
    `aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_one_fluctuationCardinalityProjectorL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            1).toLinearMap) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      1 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2

/-- The actual cardinality-one joint-sector sum has rank at least `aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_fluctuationCardinalityJointSectorSumSubmoduleL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          1) := by
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      1 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2

/-- Compact receipt for the first positive-cardinality infinite-rank sector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneEigenspaceInfiniteRankActualL2Receipt :
    Prop :=
  LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2 ∧
    (∀ n : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2
          n ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          {periodicHypercubicThreeOriginAxisZeroTarget}) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          1) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            1).toLinearMap) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          1)

/-- The actual eigenvalue-one infinite-rank receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneEigenspaceInfiniteRankActualL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneEigenspaceInfiniteRankActualL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankOneLinkPowerFluctuationL2_linearIndependent,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_oneInfiniteRankOneLinkPowerFluctuationL2_mem_singleton_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_heatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_one_fluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_one_fluctuationCardinalityJointSectorSumSubmoduleL2⟩

end

end MathlibAnalytic
end MGAP4D
