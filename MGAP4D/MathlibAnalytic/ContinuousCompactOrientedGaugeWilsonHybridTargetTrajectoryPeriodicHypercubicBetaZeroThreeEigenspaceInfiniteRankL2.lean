import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroTwoEigenspaceInfiniteRankL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityThreeTripleWitnessL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- Generic product-lift principle: if a linear recovery map sends a family
obtained by multiplying on the right by one fixed bounded-continuous factor to a
linearly independent family, then the product family is linearly independent. -/
theorem boundedContinuousFunction_mul_right_linearIndependent_of_linearMap_recovers
    {X κ W : Type*}
    [TopologicalSpace X]
    [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    (u : κ → BoundedContinuousFunction X ℝ)
    (g : BoundedContinuousFunction X ℝ)
    (recover : BoundedContinuousFunction X ℝ →ₗ[ℝ] W)
    (w : κ → W)
    (hRecover : ∀ k : κ, recover (u k * g) = w k)
    (hLinearIndependent : LinearIndependent ℝ w) :
    LinearIndependent ℝ (fun k : κ => u k * g) := by
  apply LinearIndependent.of_comp recover
  have hEq :
      (fun k : κ => recover (u k * g)) = w := by
    funext k
    exact hRecover k
  rw [hEq]
  exact hLinearIndependent

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_threeInfiniteRankEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- The target-centered two-coordinate family remains constant along every
physical coordinate outside its target/source pair. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_offLinkFiberConstant_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n) := by
  let F :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF
      n
  let PF :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
      periodicHypercubicThreeOriginAxisZeroTarget F
  let G :=
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
  have hFFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        edge F := by
    intro A B hAgree
    simp only [F,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankTargetWilsonEnergyPositivePowerBCF,
      BoundedContinuousFunction.coe_pow, Pi.pow_apply,
      periodicHypercubicThreeSpecialUnitaryTwoTargetWilsonEnergyBCF_apply]
    rw [hAgree periodicHypercubicThreeOriginAxisZeroTarget (Ne.symm hTarget)]
  have hPFFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        edge PF := by
    rw [← continuous_compact_oriented_singleLinkHeatBathProjection_fixed_iff
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge PF]
    calc
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          edge PF =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          periodicHypercubicThreeOriginAxisZeroTarget
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
            edge F) := by
              exact
                periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathProjection_pairwise_comm
                  edge periodicHypercubicThreeOriginAxisZeroTarget F
      _ = PF := by
        rw [continuous_compact_oriented_singleLinkHeatBathProjection_fixes
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge F hFFiber]
  have hGFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        edge G :=
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      edge hSource
  intro A B hAgree
  change (F A - PF A) * G A = (F B - PF B) * G B
  rw [hFFiber A B hAgree, hPFFiber A B hAgree, hGFiber A B hAgree]

/-- Replace the canonical third physical coordinate by the central negative
identity while leaving all other links unchanged. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
    A
    periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
    specialUnitaryTwoNegativeIdentity

/-- Replacing the third coordinate preserves every off-third coordinate. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration_agreeOffLink
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.AgreeOffLink
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration A)
      A
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget := by
  intro edge hEdge
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration,
    CompactOrientedGaugeWilsonSystem.replaceLink, hEdge]

/-- Multiply the countable target/source pair family by the fixed centered third
coordinate. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF
    (n : ℕ) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n *
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget

/-- Eight-point normalized rectangular recovery: first take the existing
normalized target/source rectangle at third coordinate `-1`, subtract the same
rectangle at third coordinate `1`, then divide by the third-coordinate jump. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleDifferenceLinearMap :
    BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ →ₗ[ℝ]
      (ℕ → ℝ) where
  toFun H m :=
    (((H
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration
              m)) -
        H
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration) -
        H
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration
              m)) +
        H
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration)) / 2) -
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap
        H m) / 2
  map_add' H K := by
    funext m
    simp
    ring
  map_smul' a H := by
    funext m
    simp
    ring

/-- The centered third coordinate changes by exactly two between the negative
third-coordinate background and the identity background. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankCenteredThirdCoordinate_negative_sub_identity_eq_two :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration) -
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration =
      2 := by
  have hNegative :
      specialUnitaryWilsonPlaquetteEnergy 2 specialUnitaryTwoNegativeIdentity = 2 := by
    norm_num [specialUnitaryTwoNegativeIdentity,
      specialUnitaryWilsonPlaquetteEnergy, Matrix.trace, Matrix.one_apply,
      Fin.sum_univ_two]
  change
    (specialUnitaryWilsonPlaquetteEnergy 2
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration)
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget) -
      specialUnitaryTwoWilsonEnergyHaarMean) -
      (specialUnitaryWilsonPlaquetteEnergy 2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget) -
        specialUnitaryTwoWilsonEnergyHaarMean) = 2
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration,
    CompactOrientedGaugeWilsonSystem.replaceLink, hNegative,
    specialUnitaryWilsonPlaquetteEnergy_two_one]

/-- The eight-point recovery map returns the original positive-power sequence
from every three-coordinate product-family member. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleDifferenceLinearMap_apply
    (n m : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleDifferenceLinearMap
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)
        m =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
  let F :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n
  let G :=
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
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
  let NARN :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
      ARN
  let NAIN :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
      AIN
  let NAR :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
      AR
  let NAI :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration
      AI
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget F :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_offLinkFiberConstant_of_ne
      n periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget
  have hFNARN : F NARN = F ARN :=
    hFiber NARN ARN
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration_agreeOffLink
        ARN)
  have hFNAIN : F NAIN = F AIN :=
    hFiber NAIN AIN
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration_agreeOffLink
        AIN)
  have hFNAR : F NAR = F AR :=
    hFiber NAR AR
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration_agreeOffLink
        AR)
  have hFNAI : F NAI = F AI :=
    hFiber NAI AI
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration_agreeOffLink
        AI)
  have hGNARN : G NARN = G NAI := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [NARN, NAI,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink]
  have hGNAIN : G NAIN = G NAI := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [NAIN, NAI,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink]
  have hGNAR : G NAR = G NAI := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [NAR, NAI,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankThirdNegativeConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink]
  have hGARN : G ARN = G AI := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [ARN, AI,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankRationalRotationSourceNegativeConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget]
  have hGAIN : G AIN = G AI := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [AIN, AI,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankSourceNegativeIdentityConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget]
  have hGAR : G AR = G AI := by
    apply
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
    simp [AR, AI,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankRationalRotationConfiguration,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankIdentityConfiguration,
      CompactOrientedGaugeWilsonSystem.replaceLink,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget]
  have hPairDifference :
      (F ARN - F AIN - F AR + F AI) / 2 =
        specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankDoubleDifferenceLinearMap_apply_pairBCF
        n m
  have hThirdJump : G NAI - G AI = 2 := by
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankCenteredThirdCoordinate_negative_sub_identity_eq_two
  change
    ((((F NARN * G NARN - F NAIN * G NAIN -
        F NAR * G NAR + F NAI * G NAI) / 2) -
      ((F ARN * G ARN - F AIN * G AIN -
        F AR * G AR + F AI * G AI) / 2)) / 2) =
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1)
  rw [hFNARN, hFNAIN, hFNAR, hFNAI,
    hGNARN, hGNAIN, hGNAR, hGARN, hGAIN, hGAR]
  calc
    ((((F ARN * G NAI - F AIN * G NAI -
        F AR * G NAI + F AI * G NAI) / 2) -
      ((F ARN * G AI - F AIN * G AI -
        F AR * G AI + F AI * G AI) / 2)) / 2) =
      (((F ARN - F AIN - F AR + F AI) / 2) *
        (G NAI - G AI)) / 2 := by ring
    _ =
      (specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) * 2) / 2 := by
        rw [hPairDifference, hThirdJump]
    _ = specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1) := by ring

/-- The three-coordinate bounded-continuous family is linearly independent. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF := by
  apply
    boundedContinuousFunction_mul_right_linearIndependent_of_linearMap_recovers
      (u := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF)
      (g := periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget)
      (recover :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleDifferenceLinearMap)
      (w := fun n : ℕ => fun m : ℕ =>
        specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence m ^ (n + 1))
  · intro n
    funext m
    exact
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleDifferenceLinearMap_apply
        n m
  · exact
      specialUnitaryTwoBetaZeroOneInfiniteRankEnergySequence_positivePowers_linearIndependent

/-- The actual countable three-coordinate Gibbs `L²` family. -/
noncomputable def
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2
    (n : ℕ) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)

/-- The actual countable three-coordinate Gibbs `L²` family is linearly
independent. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_linearIndependent :
    LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 := by
  have hMapped :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_linearIndependent.map'
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap
      (LinearMap.ker_eq_bot.mpr
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap_injective)
  simpa [Function.comp_def,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroOneInfiniteRankGibbsL2RepresentativeBCFLinearMap,
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
    using hMapped

/-- A pair-family `L²` fixed-point identity forces the corresponding concrete
bounded-continuous coordinate projection to vanish. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_projection_eq_zero_of_fluctuation_eq_self
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hFix :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n) =
      fun _ => 0 := by
  have hProjectionL2 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2 n) = 0 := by
    rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] at hFix
    exact sub_eq_self.mp hFix
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n)) = 0
      at hProjectionL2
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero] at hProjectionL2
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n) = 0 := by
    apply
      (BoundedContinuousFunction.toLp_injective
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
      using hProjectionL2
  funext A
  have hAt := congrArg
    (fun H : BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
      H A)
    hBCF
  simpa using hAt

/-- The target projection annihilates every three-coordinate family member. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_target_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) =
      fun _ => 0 := by
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        periodicHypercubicThreeOriginAxisZeroTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget.symm)
      A
  have hPairZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_projection_eq_zero_of_fluctuation_eq_self
      n periodicHypercubicThreeOriginAxisZeroTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_target_fluctuation_eq_self
        n)) A
  exact hMul.trans (by rw [hPairZero, zero_mul])

/-- The second-coordinate projection annihilates every three-coordinate family
member. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_source_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) =
      fun _ => 0 := by
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget.symm)
      A
  have hPairZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_projection_eq_zero_of_fluctuation_eq_self
      n periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairL2_source_fluctuation_eq_self
        n)) A
  exact hMul.trans (by rw [hPairZero, zero_mul])

/-- The third-coordinate projection annihilates every three-coordinate family
member. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_third_projection_eq_zero
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) =
      fun _ => 0 := by
  have hFiber :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n) :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_offLinkFiberConstant_of_ne
      n periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget
  have hComm :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n =
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget *
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n := by
    ext A
    simp [
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF,
      mul_comm]
  rw [hComm]
  funext A
  have hMul :=
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget)
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n)
      hFiber A
  have hZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget) A
  exact hMul.trans (by rw [hZero, zero_mul])

/-- A zero concrete coordinate projection makes the corresponding fluctuation
fix the Gibbs `L²` representative. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_fluctuation_eq_self_of_projection_eq_zero
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) =
        fun _ => 0) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjectionL2 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n) = 0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)) = 0
    rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) = 0 := by
      ext A
      exact congrFun hProjection A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjectionL2, sub_zero]

/-- Each selected fluctuation fixes the three-coordinate family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_target_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeOriginAxisZeroTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_fluctuation_eq_self_of_projection_eq_zero
    n periodicHypercubicThreeOriginAxisZeroTarget
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_target_projection_eq_zero n)

theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_source_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_fluctuation_eq_self_of_projection_eq_zero
    n periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_source_projection_eq_zero n)

theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_third_fluctuation_eq_self
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n :=
  periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_fluctuation_eq_self_of_projection_eq_zero
    n periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_third_projection_eq_zero n)

/-- Every unselected coordinate projection fixes the three-coordinate family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_projection_eq_self_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget)
    (hThird : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n := by
  apply continuous_compact_oriented_singleLinkHeatBathProjection_fixes
  intro A B hAgree
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n A *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget A =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF n B *
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget B
  have hPair :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroTwoInfiniteRankPairBCF_offLinkFiberConstant_of_ne
      n edge hTarget hSource A B hAgree
  have hThirdCoordinate :=
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_offLinkFiberConstant_of_ne
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget
      edge hThird A B hAgree
  rw [hPair, hThirdCoordinate]

/-- Every unselected fluctuation annihilates the three-coordinate family. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_fluctuation_eq_zero_of_ne
    (n : ℕ)
    (edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ periodicHypercubicThreeOriginAxisZeroTarget)
    (hSource : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget)
    (hThird : edge ≠
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n) = 0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n)) = 0
  rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero]
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF n := by
    ext A
    exact congrFun
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleBCF_projection_eq_self_of_ne
        n edge hTarget hSource hThird) A
  rw [hBCF, sub_self]

/-- Every member lies in the exact canonical three-coordinate joint sector. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_threeInfiniteRankTripleL2_mem_triple_fluctuationJointSector
    (n : ℕ) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        {periodicHypercubicThreeOriginAxisZeroTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
          periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  constructor
  · intro edge hEdge
    have hCases :
        edge = periodicHypercubicThreeOriginAxisZeroTarget ∨
          edge = periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget ∨
          edge = periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget := by
      simpa using hEdge
    rcases hCases with hEq | hEq | hEq
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_target_fluctuation_eq_self
          n
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_source_fluctuation_eq_self
          n
    · subst edge
      exact
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_third_fluctuation_eq_self
          n
  · intro edge hEdge
    apply
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_fluctuation_eq_zero_of_ne
        n edge
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)
    · intro hEq
      subst edge
      exact hEdge (by simp)

/-- The actual beta-zero heat-bath eigenspace at eigenvalue three has Cardinal
rank at least `aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_three_heatBathCardinalityEigenspaceL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          3) := by
  classical
  let Q := fun edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge =>
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
      edge
  have hGeneric :=
    continuousLinearMap_aleph0_le_rank_cardinalityEigenspace_of_linearIndependent_mem_jointSectorL2
      (Q := Q)
      (s := {periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget})
      (v := periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2)
      (fun edge f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_idempotent_for_commuting_family
          edge f)
      (fun target source f =>
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
          target source f)
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_linearIndependent
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_threeInfiniteRankTripleL2_mem_triple_fluctuationJointSector
  have hCard :
      ({periodicHypercubicThreeOriginAxisZeroTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
        periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget} :
          Finset
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge).card = 3 := by
    simp [
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget_ne,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_originAxisZeroTarget,
      periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget_ne_secondTarget]
  rw [hCard] at hGeneric
  simpa [Q,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_univ_sum_fluctuationL2]
    using hGeneric

/-- The range of the actual cardinality-three projector has rank at least
`aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_three_fluctuationCardinalityProjectorL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            3).toLinearMap) := by
  classical
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
      3 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_three_heatBathCardinalityEigenspaceL2

/-- The actual cardinality-three joint-sector sum has rank at least `aleph0`. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_three_fluctuationCardinalityJointSectorSumSubmoduleL2 :
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          3) := by
  classical
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
      3 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_three_heatBathCardinalityEigenspaceL2

/-- Compact receipt for the cardinality-three infinite-rank sector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeEigenspaceInfiniteRankL2Receipt :
    Prop :=
  LinearIndependent ℝ
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 ∧
    (∀ n : ℕ,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2 n ∈
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
          {periodicHypercubicThreeOriginAxisZeroTarget,
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityTwoSecondTarget,
            periodicHypercubicThreeSpecialUnitaryTwoCardinalityThreeThirdTarget}) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
          3) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            3).toLinearMap) ∧
    Cardinal.aleph0 ≤
      Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          3)

/-- The actual eigenvalue-three infinite-rank receipt is proved. -/
theorem
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeEigenspaceInfiniteRankL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeEigenspaceInfiniteRankL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroThreeInfiniteRankTripleL2_linearIndependent,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_threeInfiniteRankTripleL2_mem_triple_fluctuationJointSector,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_three_heatBathCardinalityEigenspaceL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_range_three_fluctuationCardinalityProjectorL2,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_aleph0_le_rank_three_fluctuationCardinalityJointSectorSumSubmoduleL2⟩

end

end MathlibAnalytic
end MGAP4D
