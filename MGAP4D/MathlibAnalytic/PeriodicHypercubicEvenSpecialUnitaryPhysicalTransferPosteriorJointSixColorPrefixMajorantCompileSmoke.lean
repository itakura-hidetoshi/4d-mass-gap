import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSixColorPrefixMajorant

/-! Regression contracts for the actual fixed-color and six-color carriers. -/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

open GroundStatePosteriorJoint

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "BoundedRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "LocalProfile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile H N hN beta hbeta
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff

-- Arbitrary fixed-color schedules, including repetitions, use the same order.
example (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    posteriorScheduleL2 H N hN beta hbeta (pre.map Subtype.val) F hF bound hbound =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
        H N hN beta hbeta color pre (BoundedRep F hF bound hbound) :=
  posteriorScheduleL2_eq_fixedColorStage H N hN beta hbeta color pre F hF bound hbound

-- Freshness is on the actual link carrier, not only on a subtype.
example (e : Link) : e ∉ posteriorSixColorPrefixLinks H e :=
  posteriorSixColorPrefixLinks_fresh H e

-- The local-profile square is the genuine posterior integral, not a proxy norm.
example (e : Link) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    LocalProfile (BoundedRep F hF bound hbound) e ^ 2 =
      posteriorStageResidualEnergy H N hN beta hbeta
        (posteriorSixColorPrefixLinks H e) e F :=
  sixColorLocalProfile_sq_eq_posteriorStageEnergy H N hN beta hbeta e F hF bound hbound

-- The standard dense-core BCF representative is the same initial vector.
example (F : BoundedContinuousFunction Joint ℝ) :
    BoundedRep F F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm = BCFRep F :=
  jointBCF_boundedConcreteL2_eq_standardRepresentative H N hN beta hbeta F

-- A canonical statement with the normalization and actual prefix fully exposed.
example (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |F (B, A) - F (B, C)| ≤ v e) :
    Profile (BCFRep F) ≤ (1 / 6 : ℝ) * ∑ e : Link,
      canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut
        (posteriorSixColorPrefixLinks H e) v e ^ 2 := by
  exact sixColorProfileEnergy_le_canonicalPrefixOscillationEnergy
    H N hN beta hbeta s hs hcut F v hv hV

-- No initial variation premise is needed for the constructed 2*sup-norm fallback.
example (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (F : BoundedContinuousFunction Joint ℝ) :
    Profile (BCFRep F) ≤ (1 / 6 : ℝ) * ∑ e : Link,
      canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut
        (posteriorSixColorPrefixLinks H e) (fun _ => 2 * ‖F‖) e ^ 2 := by
  exact sixColorProfileEnergy_le_canonicalUniformPrefixOscillationEnergy
    H N hN beta hbeta s hs hcut F

#check posteriorFixedColorPrefix_split
#check posteriorSixColorPrefixLinks_fresh
#check posteriorScheduleL2_eq_fixedColorStage
#check sixColorLocalProfile_sq_eq_posteriorStageEnergy
#check sixColorProfileEnergy_eq_posteriorStageEnergy_sum
#check sixColorLocalProfile_le_variationProfile
#check sixColorProfileEnergy_le_canonicalPrefixOscillationEnergy
#check sixColorProfileEnergy_le_canonicalUniformPrefixOscillationEnergy

#print axioms posteriorFixedColorPrefix_split
#print axioms posteriorFixedColorPrefix_fresh
#print axioms posteriorSixColorPrefixLinks_fresh
#print axioms fixedColorStage_eq_projectionSchedule
#print axioms posteriorScheduleL2_eq_fixedColorStage
#print axioms jointBCF_boundedConcreteL2_eq_standardRepresentative
#print axioms sixColorLocalProfile_sq_eq_posteriorStageEnergy
#print axioms sixColorProfileEnergy_eq_posteriorStageEnergy_sum
#print axioms posteriorSixColorVariationProfile_nonneg
#print axioms sixColorLocalProfile_le_variationProfile
#print axioms sixColorProfileEnergy_le_variationOscillationEnergy
#print axioms sixColorProfileEnergy_le_canonicalPrefixOscillationEnergy
#print axioms sixColorProfileEnergy_le_canonicalUniformPrefixOscillationEnergy

end

end MGAP4D.MathlibAnalytic
