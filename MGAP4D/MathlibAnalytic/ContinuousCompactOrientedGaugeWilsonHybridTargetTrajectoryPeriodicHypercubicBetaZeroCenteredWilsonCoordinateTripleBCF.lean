import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityThreeTripleProfileL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCenteredWilsonCoordinatePairBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityThreeTripleEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- Product of three centered physical-link Wilson-coordinate observables. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    BoundedContinuousFunction
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ :=
  periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target *
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
      source third

@[simp]
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_apply
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
        target source third A =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target A *
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF source A *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF third A) := by
  rfl

/-- A centered pair observable is constant on a fourth coordinate fiber. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_offLinkFiberConstant_of_ne
    (target source edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
        target source) := by
  intro A B hAgree
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_apply]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
      target A B (hAgree target (Ne.symm hTarget)),
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
      source A B (hAgree source (Ne.symm hSource))]

/-- A centered triple observable is constant along every unselected physical
link fiber. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_offLinkFiberConstant_of_ne
    (target source third edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source)
    (hThird : edge ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.OffLinkFiberConstant
      edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
        target source third) := by
  intro A B hAgree
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_apply]
  rw [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
      target A B (hAgree target (Ne.symm hTarget)),
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
      source A B (hAgree source (Ne.symm hSource)),
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_eq_of_apply_eq
      third A B (hAgree third (Ne.symm hThird))]

/-- The centered triple product is nonzero for three pairwise distinct links. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_ne_zero
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
        target source third ≠ 0 := by
  intro hZero
  let A0 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    fun _ => 1
  let A1 :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.replaceLink
          A0 target specialUnitaryTwoNegativeIdentity)
        source specialUnitaryTwoNegativeIdentity)
      third specialUnitaryTwoNegativeIdentity
  have hAt0 := congrArg
    (fun F : BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
      F A0)
    hZero
  have hAt1 := congrArg
    (fun F : BoundedContinuousFunction
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration ℝ =>
      F A1)
    hZero
  have hA1Target : A1 target = specialUnitaryTwoNegativeIdentity := by
    simp [A1, A0, CompactOrientedGaugeWilsonSystem.replaceLink,
      hTargetSource, hTargetThird]
  have hA1Source : A1 source = specialUnitaryTwoNegativeIdentity := by
    simp [A1, A0, CompactOrientedGaugeWilsonSystem.replaceLink, hSourceThird]
  have hA1Third : A1 third = specialUnitaryTwoNegativeIdentity := by
    simp [A1, A0, CompactOrientedGaugeWilsonSystem.replaceLink]
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    A0] at hAt0
  simp [
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_apply,
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_apply,
    hA1Target, hA1Source, hA1Third] at hAt1
  have hEnergyOne :
      specialUnitaryWilsonPlaquetteEnergy 2
          (1 : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge) = 0 := by
    change specialUnitaryWilsonPlaquetteEnergy 2
      (1 : SpecialUnitaryMatrixGroup 2) = 0
    exact specialUnitaryWilsonPlaquetteEnergy_two_one
  rw [hEnergyOne, zero_sub] at hAt0
  have hNegMean : -specialUnitaryTwoWilsonEnergyHaarMean = 0 := hAt0
  have hMeanZero : specialUnitaryTwoWilsonEnergyHaarMean = 0 :=
    neg_eq_zero.mp hNegMean
  rw [hMeanZero] at hAt1
  norm_num at hAt1

/-- Averaging the triple observable in its first selected coordinate gives
zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_target_eq_zero
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hTargetThird : target ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third) =
      fun _ => 0 := by
  funext A
  change
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        target
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target *
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF
            source third)
        A = 0
  rw [
    continuous_compact_oriented_singleLinkHeatBathProjection_mul_of_right_offLinkFiberConstant
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      target
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF target)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF source third)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinatePairBCF_offLinkFiberConstant_of_ne
        source third target hTargetSource hTargetThird)
      A]
  have hZero := congrFun
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateBCF_projection_self_eq_zero
      target) A
  rw [hZero, zero_mul]

/-- Averaging the triple observable in its second selected coordinate gives
zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_source_eq_zero
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetSource : target ≠ source)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        source
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third) =
      fun _ => 0 := by
  have hReorder :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third =
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          source target third := by
    ext A
    simp [periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_apply]
    ring
  rw [hReorder]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_target_eq_zero
      source target third hTargetSource.symm hSourceThird

/-- Averaging the triple observable in its third selected coordinate gives
zero. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_third_eq_zero
    (target source third :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTargetThird : target ≠ third)
    (hSourceThird : source ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        third
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third) =
      fun _ => 0 := by
  have hReorder :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third =
        periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          third target source := by
    ext A
    simp [periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_apply]
    ring
  rw [hReorder]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_target_eq_zero
      third target source hTargetThird.symm hSourceThird.symm

/-- Every unselected coordinate projection fixes the triple observable. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_projection_eq_self_of_ne
    (target source third edge :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hTarget : edge ≠ target)
    (hSource : edge ≠ source)
    (hThird : edge ≠ third) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjection
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
          target source third) =
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
        target source third := by
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_fixes
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem edge
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF
        target source third)
      (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateTripleBCF_offLinkFiberConstant_of_ne
        target source third edge hTarget hSource hThird)

end

end MathlibAnalytic
end MGAP4D
