import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroOneEigenspaceInfiniteRankActualL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityTwoPairWitnessL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_twoInfiniteRankEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The identity background with the canonical second physical coordinate set
to the central negative identity. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
    specialUnitaryTwoNegativeIdentity

/-- The rational target rotation with the canonical second physical coordinate
set to the central negative identity. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
      n)
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
    specialUnitaryTwoNegativeIdentity

/-- The uncentered two-coordinate product: a positive target-energy power times
the fixed centered Wilson coordinate at the canonical second edge. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
      n *
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget

/-- Center only the target factor, retaining the fixed centered second-coordinate
factor. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
      n *
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget

/-- The target-centered factor has the same positive-power difference when the
second coordinate is fixed at the central negative identity. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPowerFluctuationBCF_sourceNegative_difference
    (n m : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
        n
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
          m) -
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
        n
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
  have hAgree :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.AgreeOffLink
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
          m)
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration
        periodicHypercubicThreeOriginAxisZeroTarget := by
    intro edge hEdge
    simp [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink,
      hEdge]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
            m) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration :=
    continuous_compact_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
        m)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration
      hAgree
  have hRotation :
      specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
            m periodicHypercubicThreeOriginAxisZeroTarget) =
        specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m := by
    rw [show
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
          m periodicHypercubicThreeOriginAxisZeroTarget =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
          m periodicHypercubicThreeOriginAxisZeroTarget by
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration,
        CompactOrientedGaugeWilsonSystem.replaceLink,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne]]
    simpa only [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply] using
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_betaZeroOneInfiniteRankRationalRotationConfiguration
        m
  have hIdentity :
      specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration
            periodicHypercubicThreeOriginAxisZeroTarget) = 0 := by
    rw [show
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration
          periodicHypercubicThreeOriginAxisZeroTarget =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
          periodicHypercubicThreeOriginAxisZeroTarget by
      simp [
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration,
        CompactOrientedGaugeWilsonSystem.replaceLink,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne]]
    simpa only [periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply] using
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_betaZeroOneInfiniteRankIdentityConfiguration
  change
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
          m) -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n)
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
          m)) -
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n)
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration) =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1)
  rw [hProjection]
  ring_nf
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF,
    hRotation, hIdentity, pow_succ, mul_comm]

/-- The fixed centered second-coordinate factor changes by exactly two between
the central negative identity and the identity. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankCenteredSecondCoordinate_negative_sub_identity_eq_two :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration -
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration =
      2 := by
  change
    (specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) -
      specialUnitaryTwoWilsonEnergyHaarMean) -
      (specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) -
        specialUnitaryTwoWilsonEnergyHaarMean) = 2
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration,
    CompactOrientedGaugeWilsonSystem.replaceLink,
    specialUnitaryTwoNegativeIdentity,
    specialUnitaryWilsonPlaquetteEnergy,
    Matrix.trace,
    Fin.sum_univ_two]

/-- Rectangular second-difference evaluation in the target and fixed second
coordinates.  Division by two normalizes the explicit second-coordinate jump. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      (ℕ → ℝ) where
  toFun F m :=
    (F
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
          m) -
      F periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration -
      F
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
          m) +
      F periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration) / 2
  map_add' F G := by
    funext m
    simp
    ring
  map_smul' a F := by
    funext m
    simp
    ring

/-- The double-difference map recovers the same positive-power sequence from
the two-coordinate product family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap_apply_pairBCF
    (n m : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n)
        m =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
  let F :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPowerFluctuationBCF
      n
  let G :=
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
  let ARN :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
      m
  let AIN :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration
  let AR :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
      m
  let AI :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
  have hFNeg : F ARN - F AIN =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPowerFluctuationBCF_sourceNegative_difference
        n m
  have hFIdentity : F AR - F AI =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankDifferenceEvaluationLinearMap_apply_powerFluctuationBCF
        n m
  have hGNeg : G ARN = G AIN := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [ARN, AIN,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink]
  have hGIdentity : G AR = G AI := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [AR, AI,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne]
  have hGJump : G AIN - G AI = 2 := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankCenteredSecondCoordinate_negative_sub_identity_eq_two
  change
    (F ARN * G ARN - F AIN * G AIN -
      F AR * G AR + F AI * G AI) / 2 =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1)
  rw [hGNeg, hGIdentity]
  calc
    ((F ARN * G AIN - F AIN * G AIN -
        F AR * G AI + F AI * G AI) / 2) =
      (((F ARN - F AIN) * G AIN -
        (F AR - F AI) * G AI) / 2) := by ring
    _ =
      ((specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) * G AIN -
        specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) * G AI) / 2) := by
          rw [hFNeg, hFIdentity]
    _ = specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
      rw [← mul_sub, hGJump]
      ring

/-- The two-coordinate bounded-continuous product family is linearly
independent. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF := by
  apply LinearIndependent.of_comp
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap
  change
    LinearIndependent ℝ
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n))
  have hPointwise :
      (fun n : ℕ =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n)) =
        (fun n : ℕ => fun m : ℕ =>
          specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1)) := by
    funext n m
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap_apply_pairBCF
        n m
  rw [hPointwise]
  exact
    specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_positivePowers_linearIndependent

/-- The target projection of the uncentered pair factors through the fixed
second-coordinate observable. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF_target_projection_apply
    (n : ℕ)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n)
        A =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n)
          A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget A := by
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm)
      A

/-- The centered pair is exactly the uncentered pair minus its target-coordinate
conditional expectation. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_eq_raw_sub_targetProjection
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n) := by
  ext A
  have hProjection :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF_target_projection_apply
      n A
  change
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n A -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n) A) *
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget A) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n A -
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n) A
  rw [hProjection]
  change
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n A -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n) A) *
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget A) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget A -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
            n) A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget A
  ring

/-- The actual countable two-coordinate Gibbs `L²` family. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2
    (n : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n)

/-- The actual countable two-coordinate Gibbs `L²` family is linearly
independent. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 := by
  have hMapped :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_linearIndependent.map'
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap
      (LinearMap.ker_eq_bot.mpr
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap_injective)
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap,
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
    using hMapped

/-- The two-coordinate family is the target fluctuation of the uncentered pair
representative. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_eq_target_fluctuation
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n)) := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_eq_raw_sub_targetProjection]
  exact map_sub
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n))

/-- The target fluctuation fixes every member of the two-coordinate family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_target_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_eq_target_fluctuation]
  exact
    continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply_fluctuation
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeOriginAxisZeroTarget _

/-- The source projection annihilates the uncentered pair. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF_source_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n) =
      fun _ => 0 := by
  funext A
  have hRawFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
          n) := by
    intro B D hAgree
    simp only [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF,
      BoundedContinuousFunction.coe_pow, Pi.pow_apply,
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply]
    rw [hAgree periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne]
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n)
      hRawFiber A
  have hZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) A
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (fun B =>
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
              periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget B *
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
              n B)
        A = 0
  rw [hMul, hZero, zero_mul]

/-- The second-coordinate fluctuation fixes the uncentered pair representative. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairL2_source_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n)) =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n) := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n) = 0 := by
    ext A
    exact congrFun
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF_source_projection_eq_zero
        n) A
  rw [hBCF]
  simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]

/-- The second-coordinate fluctuation fixes every member of the target-centered
pair family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_source_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_eq_target_fluctuation]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeOriginAxisZeroTarget]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairL2_source_fluctuation_eq_self]

/-- Every unselected coordinate projection fixes the uncentered pair. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF_projection_eq_self_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠ periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n := by
  apply continuous_compact_oriented_singleLinkHeatBathProjection_fixes
  intro A B hAgree
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n A *
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget A =
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
        n B *
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget B
  congr 1
  · simp only [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF,
      BoundedContinuousFunction.coe_pow, Pi.pow_apply,
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply]
    rw [hAgree periodicHypercubicThreeOriginAxisZeroTarget (Ne.symm hTarget)]
  · apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    exact hAgree periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      (Ne.symm hSource)

/-- Every unselected fluctuation annihilates the uncentered pair representative. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠ periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n)) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF n := by
    ext A
    exact congrFun
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairBCF_projection_eq_self_of_ne
        n edge hTarget hSource) A
  rw [hBCF, sub_self]

/-- Every unselected fluctuation annihilates the target-centered pair family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠ periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n) = 0 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_eq_target_fluctuation]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
      edge periodicHypercubicThreeOriginAxisZeroTarget]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRawPairL2_fluctuation_eq_zero_of_ne
      n edge hTarget hSource]
  simp

/-- Every member of the countable family lies in the exact two-coordinate joint
sector. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoInfiniteRankPairL2_mem_pair_fluctuationJointSector
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {periodicHypercubicThreeOriginAxisZeroTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget} := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases :
        edge = periodicHypercubicThreeOriginAxisZeroTarget ∨
          edge = periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget := by
      simpa using hEdge
    rcases hCases with hEq | hEq
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_target_fluctuation_eq_self
          n
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_source_fluctuation_eq_self
          n
  · intro edge hEdge
    apply
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_fluctuation_eq_zero_of_ne
        n edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- The actual beta-zero heat-bath eigenspace at eigenvalue two has Cardinal rank
at least `aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_two_heatBathCardinalityEigenspaceL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          2) := by
  classical
  let Q := fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      edge
  have hGeneric :=
    continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
      (Q := Q)
      (s := {periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget})
      (v := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2)
      (fun edge f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge f)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_linearIndependent
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoInfiniteRankPairL2_mem_pair_fluctuationJointSector
  simpa [Q,
    finset_pair_card_eq_two
      periodicHypercubicThreeOriginAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne.symm,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
    using hGeneric

/-- The range of the actual cardinality-two projector has rank at least
`aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_two_fluctuationCardinalityProjectorL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            2).toLinearMap) := by
  classical
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      2 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_two_heatBathCardinalityEigenspaceL2

/-- The actual cardinality-two joint-sector sum has rank at least `aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_two_fluctuationCardinalityJointSectorSumSubmoduleL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          2) := by
  classical
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      2 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_two_heatBathCardinalityEigenspaceL2

/-- Compact receipt for the cardinality-two infinite-rank sector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoEigenspaceInfiniteRankL2Receipt :
    Prop :=
  LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 ∧
    (∀ n : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          {periodicHypercubicThreeOriginAxisZeroTarget,
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget}) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          2) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            2).toLinearMap) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          2)

/-- The actual eigenvalue-two infinite-rank receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoEigenspaceInfiniteRankL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoEigenspaceInfiniteRankL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_linearIndependent,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_twoInfiniteRankPairL2_mem_pair_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_two_heatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_two_fluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_two_fluctuationCardinalityJointSectorSumSubmoduleL2⟩

end

end MathlibAnalytic
end MGAP4D
