import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointInitialEnergyFloor

/-!
# Remove the unchanged left-boundary component before taking a sup-norm bound

The uncentered uniform fallback cannot improve the norm bound. A concrete
alternative keeps the same BCF approximation O but measures only the remainder

  O(L,R) - O(L,1).

The anchored term is a genuinely constructed joint BCF depending only on L.
It cancels in every right-link difference. Its propagated profile is zero, and
its standard joint-L2 representative is in the kernel of the actual normalized
stage residual operator. Thus removing it preserves the genuine profile exactly.

The centered initial bound and the resulting full-L2 continuous majorant are
constructed, not assumed. No small remainder, localized approximation of the
frozen family, physicality, or transfer identification is asserted. The anchor
is the identity configuration, not a claim about the physical vacuum.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

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
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "T" => sixColorResidualOperator H N hN beta hbeta
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "Majorant" => bcfApproximationMajorant H N hN beta hbeta

/-- Canonical right anchor, retaining all left-boundary dependence. -/
def posteriorRightAnchorBCF (O : BoundedContinuousFunction Joint ℝ) :
    BoundedContinuousFunction Joint ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => O (z.1, (fun _ => 1)),
      O.continuous.comp (continuous_fst.prodMk continuous_const)⟩

/-- Evaluation at the identity right configuration is literal, not only a.e. -/
theorem posteriorRightAnchorBCF_apply (O : BoundedContinuousFunction Joint ℝ) (z : Joint) :
    posteriorRightAnchorBCF H N O z = O (z.1, (fun _ => 1)) := rfl

/-- Anchoring twice does not change the chosen left-boundary function. -/
theorem posteriorRightAnchorBCF_idempotent (O : BoundedContinuousFunction Joint ℝ) :
    posteriorRightAnchorBCF H N (posteriorRightAnchorBCF H N O) =
      posteriorRightAnchorBCF H N O := by
  ext z
  rfl

/-- Constructed initial profile after removing the unchanged left component. -/
def rightAnchoredInitialVariation (O : BoundedContinuousFunction Joint ℝ) : Link → ℝ :=
  fun _ => 2 * ‖O - posteriorRightAnchorBCF H N O‖

/-- The centered initial profile has the required sign. -/
theorem rightAnchoredInitialVariation_nonneg (O : BoundedContinuousFunction Joint ℝ) (e : Link) :
    0 ≤ rightAnchoredInitialVariation H N O e :=
  mul_nonneg (by norm_num) (norm_nonneg _)

/-- Only the remainder contributes to any right-link difference. In fact this
bound holds for any two right configurations at the same left boundary. -/
theorem rightAnchoredInitialVariation_bound (O : BoundedContinuousFunction Joint ℝ)
    (B : Cfg) (e : Link) (A C : Cfg) :
    |O (B, A) - O (B, C)| ≤ rightAnchoredInitialVariation H N O e := by
  have h := jointBCF_variation_le_two_norm H N (O - posteriorRightAnchorBCF H N O) B A C
  change |(O (B, A) - O (B, (fun _ => 1))) -
    (O (B, C) - O (B, (fun _ => 1)))| ≤
      2 * ‖O - posteriorRightAnchorBCF H N O‖ at h
  have hCancel : (O (B, A) - O (B, (fun _ => 1))) -
      (O (B, C) - O (B, (fun _ => 1))) = O (B, A) - O (B, C) := by ring
  rw [hCancel] at h
  exact h

/-- An automatic full-L2 majorant; no initial or final oscillation bound is
assumed. Its continuity is already given by bcfApproximationMajorant_continuous. -/
theorem sixColorProfileEnergy_le_rightAnchoredMajorant (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    Profile f ≤ Majorant R O (rightAnchoredInitialVariation H N O) f := by
  apply sixColorProfileEnergy_le_bcfApproximationMajorant H N hN beta hbeta R O
    (rightAnchoredInitialVariation H N O)
    (rightAnchoredInitialVariation_nonneg H N O)
  intro B e A C _hAgree
  exact rightAnchoredInitialVariation_bound H N O B e A C

/-- The centered majorant is zero at every anchored BCF center, even when its
sup-norm and L2 norm are nonzero. The uncentered fallback cannot do this. -/
theorem rightAnchoredMajorant_at_anchor (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) :
    Majorant R (posteriorRightAnchorBCF H N O)
      (rightAnchoredInitialVariation H N (posteriorRightAnchorBCF H N O))
      (BCFRep (posteriorRightAnchorBCF H N O)) = 0 := by
  simp [bcfApproximationMajorant, rightAnchoredInitialVariation,
    posteriorRightAnchorBCF_idempotent, posteriorSixColorVariationProfile,
    posteriorVariationSchedule_zero,
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy]

/-- The actual profile annihilates every constructed left-boundary BCF. -/
theorem sixColorProfileEnergy_rightAnchor_eq_zero (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) :
    Profile (BCFRep (posteriorRightAnchorBCF H N O)) = 0 := by
  apply le_antisymm _ (sixColorProfileEnergy_nonneg H N hN beta hbeta _)
  have h := sixColorProfileEnergy_le_rightAnchoredMajorant H N hN beta hbeta R
    (posteriorRightAnchorBCF H N O) (BCFRep (posteriorRightAnchorBCF H N O))
  rw [rightAnchoredMajorant_at_anchor] at h
  exact h

/-- The kernel statement concerns only the posterior stage residual operator,
not the physical transfer or a coarse physical range. -/
theorem sixColorResidualOperator_rightAnchor_eq_zero (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) :
    T (BCFRep (posteriorRightAnchorBCF H N O)) = 0 := by
  apply norm_eq_zero.mp
  have h := sixColorResidualOperator_norm_sq H N hN beta hbeta
    (BCFRep (posteriorRightAnchorBCF H N O))
  rw [sixColorProfileEnergy_rightAnchor_eq_zero H N hN beta hbeta R O] at h
  nlinarith [norm_nonneg (T (BCFRep (posteriorRightAnchorBCF H N O)))]

/-- Subtracting the explicitly anchored part preserves the genuine residuals
on the whole original joint Hilbert space. -/
theorem sixColorResidualOperator_sub_rightAnchor (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    T (f - BCFRep (posteriorRightAnchorBCF H N O)) = T f := by
  rw [map_sub, sixColorResidualOperator_rightAnchor_eq_zero H N hN beta hbeta R O, sub_zero]

/-- Exact energy preservation, with no comparison or density coefficient. -/
theorem sixColorProfileEnergy_sub_rightAnchor (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    Profile (f - BCFRep (posteriorRightAnchorBCF H N O)) = Profile f := by
  rw [← sixColorResidualOperator_norm_sq, sixColorResidualOperator_sub_rightAnchor H N hN beta hbeta R O f,
    sixColorResidualOperator_norm_sq]

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
