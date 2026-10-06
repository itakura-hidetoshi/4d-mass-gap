import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointPrefixVariationMajorant
import MGAP4D.MathlibAnalytic.PeriodHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileBoundedContinuousCoreClosure

/-!
# Constructed posterior prefix bounds on the genuine six-color stage profile

Each spatial link uses the prefix before its occurrence in its own fixed-color
canonical enumeration. The six color sweeps all start from the SAME input.
Mapping subtype links to actual links preserves the chronological schedule.
The existing exact residual theorem identifies each local-profile square with
the literal posterior stage integral. Thus the constructed variation bound
from the preceding file controls the actual normalized profile with factor 1/6.

No final residual or stage-oscillation bound is assumed. Initial observable
variation is propagated using the actual posterior response data. The canonical
half-barrier specialization and the unconditional-in-observable BCF fallback
are included. No smallness, volume-uniformity, support-distance tail, physical
transfer identification, or L2-continuity of the variation bound is asserted.
-/

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

namespace GroundStatePosteriorJoint

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "Stage" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector H N hN beta hbeta
local notation "BoundedRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "LocalProfile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageOscillationEnergy H
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta

private theorem posteriorFixedColorPrefix_exists
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    ∃ pre suffix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color),
      (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
        pre ++ e :: suffix ∧ e ∉ pre := by
  classical
  exact List.eq_append_cons_of_mem (by simp)

/-- The actual prefix of the fixed-color enumeration before the target. -/
def posteriorFixedColorPrefix (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    List (PeriodicHypercubicEvenFixedSpatialColorLink H color) :=
  (posteriorFixedColorPrefix_exists H color e).choose

/-- The matching suffix, chosen together with the actual prefix. -/
def posteriorFixedColorSuffix (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    List (PeriodicHypercubicEvenFixedSpatialColorLink H color) :=
  (posteriorFixedColorPrefix_exists H color e).choose_spec.choose

/-- The constructed prefix uses exactly the pre-existing enumeration. -/
theorem posteriorFixedColorPrefix_split (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
      posteriorFixedColorPrefix H color e ++ e :: posteriorFixedColorSuffix H color e :=
  (posteriorFixedColorPrefix_exists H color e).choose_spec.choose_spec.1

/-- Freshness is constructed, not an additional premise. -/
theorem posteriorFixedColorPrefix_fresh (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    e ∉ posteriorFixedColorPrefix H color e :=
  (posteriorFixedColorPrefix_exists H color e).choose_spec.choose_spec.2

/-- Each link uses only its own fixed-color prefix; colors are not concatenated. -/
def posteriorSixColorPrefixLinks (e : Link) : List Link :=
  (posteriorFixedColorPrefix H (periodicHypercubicEvenSpatialSliceLinkColor H e)
    ⟨e, rfl⟩).map Subtype.val

/-- The actual spatial target is absent before its update. -/
theorem posteriorSixColorPrefixLinks_fresh (e : Link) :
    e ∉ posteriorSixColorPrefixLinks H e := by
  classical
  intro he
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp he
  have hxe' : x = (⟨e, rfl⟩ : PeriodicHypercubicEvenFixedSpatialColorLink H
      (periodicHypercubicEvenSpatialSliceLinkColor H e)) := Subtype.ext hxe
  exact posteriorFixedColorPrefix_fresh H _ _ (hxe' ▸ hx)

/-- Subtype erasure preserves arbitrary chronological schedules, even with repeats. -/
theorem fixedColorStage_eq_projectionSchedule
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre : List (PeriodicHypercubicEvenFixedSpatialColorLink H color)) (f : JL2) :
    Stage color pre f = realHilbertProjectionSweep PJoint (pre.map Subtype.val) f := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
  induction pre generalizing f with
  | nil => rfl
  | cons e pre ih => exact ih (PJoint e.1 f)

/-- The literal posterior prefix and the existing fixed-color stage are one L2 vector. -/
theorem posteriorScheduleL2_eq_fixedColorStage
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    posteriorScheduleL2 H N hN beta hbeta (pre.map Subtype.val) F hF bound hbound =
      Stage color pre (BoundedRep F hF bound hbound) := by
  rw [posteriorScheduleL2_eq_projectionSchedule]
  exact (fixedColorStage_eq_projectionSchedule H N hN beta hbeta color pre _).symm

/-- The bounded concrete and standard dense-core BCF maps give the same initial vector. -/
theorem jointBCF_boundedConcreteL2_eq_standardRepresentative
    (F : BoundedContinuousFunction Joint ℝ) :
    BoundedRep F F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm = BCFRep F := by
  letI : IsProbabilityMeasure μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  apply Lp.ext
  exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
    H N hN beta hbeta F F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm).trans
      (BoundedContinuousFunction.coeFn_toLp 2 μJ ℝ F).symm

/-- Exact residual adapter: no pointwise oscillation witness is substituted for an a.e. bound. -/
theorem sixColorLocalProfile_sq_eq_posteriorStageEnergy
    (e : Link) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    LocalProfile (BoundedRep F hF bound hbound) e ^ 2 =
      posteriorStageResidualEnergy H N hN beta hbeta (posteriorSixColorPrefixLinks H e) e F := by
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
      H N hN beta hbeta e
      (posteriorFixedColorPrefix H (periodicHypercubicEvenSpatialSliceLinkColor H e) ⟨e, rfl⟩)
      (posteriorFixedColorSuffix H (periodicHypercubicEvenSpatialSliceLinkColor H e) ⟨e, rfl⟩)
      (BoundedRep F hF bound hbound)
      (posteriorFixedColorPrefix_split H _ _)
      (posteriorFixedColorPrefix_fresh H _ _)
  rw [hLocal, posteriorStageResidualEnergy_eq_projectionResidualNormSq]
  simp only [posteriorSixColorPrefixLinks, posteriorScheduleL2_eq_fixedColorStage,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2]

/-- Exact normalized sum on the genuine joint carrier, with one shared initial vector. -/
theorem sixColorProfileEnergy_eq_posteriorStageEnergy_sum
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    Profile (BoundedRep F hF bound hbound) =
      (1 / 6 : ℝ) * ∑ e : Link,
        posteriorStageResidualEnergy H N hN beta hbeta (posteriorSixColorPrefixLinks H e) e F := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
  congr 1
  exact Finset.sum_congr rfl fun e _ =>
    sixColorLocalProfile_sq_eq_posteriorStageEnergy H N hN beta hbeta e F hF bound hbound

/-- The constructed stage-dependent influence profile at each link's actual prefix. -/
def posteriorSixColorVariationProfile (R : ResponseData) (v : Link → ℝ) (e : Link) : ℝ :=
  posteriorVariationSchedule H
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
      H beta R.epsilon) (posteriorSixColorPrefixLinks H e) v e

/-- The propagated profile has the sign required by the existing energy receiver. -/
theorem posteriorSixColorVariationProfile_nonneg
    (R : ResponseData) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e) (e : Link) :
    0 ≤ posteriorSixColorVariationProfile H N hN beta hbeta R v e :=
  posteriorVariationSchedule_nonneg H _
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_nonneg
      H beta R.epsilon R.epsilon_nonneg) (posteriorSixColorPrefixLinks H e) v hv e

/-- Actual local-profile amplitude from propagated INITIAL observable variation. -/
theorem sixColorLocalProfile_le_variationProfile
    (R : ResponseData) (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |F (B, A) - F (B, C)| ≤ v e) (e : Link) :
    LocalProfile (BCFRep F) e ≤ posteriorSixColorVariationProfile H N hN beta hbeta R v e := by
  have hsq : LocalProfile (BCFRep F) e ^ 2 ≤
      posteriorSixColorVariationProfile H N hN beta hbeta R v e ^ 2 := by
    rw [← jointBCF_boundedConcreteL2_eq_standardRepresentative H N hN beta hbeta F,
      sixColorLocalProfile_sq_eq_posteriorStageEnergy]
    exact posteriorStageResidualEnergy_le_variationSchedule_sq
      H N hN beta hbeta R (posteriorSixColorPrefixLinks H e) e F v hv hV
  exact (sq_le_sq₀
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
      H N hN beta hbeta (BCFRep F) e)
    (posteriorSixColorVariationProfile_nonneg H N hN beta hbeta R v hv e)).mp hsq

/-- Coefficient 1/6 is inherited unchanged; no cardinality estimate is inserted. -/
theorem sixColorProfileEnergy_le_variationOscillationEnergy
    (R : ResponseData) (F : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |F (B, A) - F (B, C)| ≤ v e) :
    Profile (BCFRep F) ≤ OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) := by
  rw [← jointBCF_boundedConcreteL2_eq_standardRepresentative H N hN beta hbeta F,
    sixColorProfileEnergy_eq_posteriorStageEnergy_sum]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageOscillationEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun e _ =>
    posteriorStageResidualEnergy_le_variationSchedule_sq
      H N hN beta hbeta R (posteriorSixColorPrefixLinks H e) e F v hv hV

/-- Canonical half-barrier specialization of the actual six-color prefix profile. -/
def canonicalPosteriorSixColorVariation (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (v : Link → ℝ) (e : Link) : ℝ :=
  canonicalPosteriorPrefixVariation H N hN beta hbeta s hs hcut
    (posteriorSixColorPrefixLinks H e) v e

/-- Constructed canonical six-color bound on the standard BCF dense core. -/
theorem sixColorProfileEnergy_le_canonicalPrefixOscillationEnergy
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (F : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |F (B, A) - F (B, C)| ≤ v e) :
    Profile (BCFRep F) ≤ OscEnergy (canonicalPosteriorSixColorVariation H N hN beta hbeta s hs hcut v) :=
  sixColorProfileEnergy_le_variationOscillationEnergy H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hs beta hbeta hcut) F v hv hV

/-- Every joint BCF has a fully constructed bound, without an initial variation premise.
This finite bound is not asserted to be small, L2-continuous, or volume-uniform. -/
theorem sixColorProfileEnergy_le_canonicalUniformPrefixOscillationEnergy
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (F : BoundedContinuousFunction Joint ℝ) :
    Profile (BCFRep F) ≤ OscEnergy (canonicalPosteriorSixColorVariation H N hN beta hbeta s hs hcut
      (fun _ => 2 * ‖F‖)) := by
  apply sixColorProfileEnergy_le_canonicalPrefixOscillationEnergy
    H N hN beta hbeta s hs hcut F (fun _ => 2 * ‖F‖)
  · intro e
    exact mul_nonneg (by norm_num) (norm_nonneg F)
  · intro B e A C hAgree
    exact jointBCF_variation_le_two_norm H N F B A C

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
