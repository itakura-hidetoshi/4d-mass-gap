import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointRightAnchoredMajorant

/-!
# Intrinsic left-boundary quotient approximation for posterior stage energy

Reuse the existing same-scale left-boundary projection Q = J_L J_L^* on the
original genuine joint L2. Every actual one-link posterior projection fixes
its range, hence the normalized stage-residual operator T annihilates Q.
The complementary projection C = I-Q therefore preserves T and profile energy.

The approximation error ||C(f-iota O)|| is the ATTAINED least error after
arbitrary left-boundary L2 corrections. It is no larger than ||f-iota O||.
Combining this error with the already constructed initial-variation energy E_v
produces the continuous scalar majorant

  (||C(f-iota O)|| + sqrt(E_v))^2.

No point evaluation of a generic L2 representative is used. This same-scale
left-boundary projection is NOT the adjacent common-marginal coarse physical
projection. No small approximation, locality tail, kernel equality, physical
transfer identification, or physical-carrier invariance is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

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
local notation "VL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2 H N hN beta hbeta
local notation "JLeft" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry H N hN beta hbeta
local notation "ALeft" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint H N hN beta hbeta
local notation "QLeft" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp H N hN beta hbeta
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "T" => sixColorResidualOperator H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "Amp" => sixColorProfileAmplitude H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy H
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff

/-- One-link projections fix the full pre-existing left-boundary L2 image.
No response matrix or small-coupling condition is needed. -/
theorem posteriorOneLink_leftBoundary_fixed (e : Link) (u : VL2) :
    PJoint e (JLeft u) = JLeft u := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_norm_le_color
      H N hN beta hbeta e (JLeft u)
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_leftBoundary_fixed,
    sub_self, norm_zero] at h
  have hz : JLeft u - PJoint e (JLeft u) = 0 :=
    norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  exact (sub_eq_zero.mp hz).symm

/-- All chronological lists, including empty lists and repeated targets, fix
left-boundary vectors. This uses no cross-link commutativity. -/
theorem posteriorProjectionSchedule_leftBoundary_fixed (pre : List Link) (u : VL2) :
    realHilbertProjectionSweep PJoint pre (JLeft u) = JLeft u := by
  induction pre with
  | nil => rfl
  | cons e pre ih =>
      change realHilbertProjectionSweep PJoint pre (PJoint e (JLeft u)) = JLeft u
      rw [posteriorOneLink_leftBoundary_fixed]
      exact ih

/-- The actual normalized residual family annihilates every left-boundary vector. -/
theorem sixColorResidualOperator_leftBoundary_eq_zero (u : VL2) : T (JLeft u) = 0 := by
  change sixColorResidualLinearMap H N hN beta hbeta (JLeft u) = 0
  rw [sixColorResidualLinearMap_apply]
  have hz : (fun e : Link =>
      realHilbertProjectionSweep PJoint (posteriorSixColorPrefixLinks H e) (JLeft u) -
        PJoint e (realHilbertProjectionSweep PJoint (posteriorSixColorPrefixLinks H e) (JLeft u))) =
      (0 : Link → JL2) := by
    funext e
    simp only [posteriorProjectionSchedule_leftBoundary_fixed,
      posteriorOneLink_leftBoundary_fixed, sub_self, Pi.zero_apply]
  rw [hz, WithLp.toLp_zero, smul_zero]

/-- The projection in this theorem is the existing SAME-SCALE left-boundary
projection, not the adjacent coarse physical projection. -/
theorem sixColorResidualOperator_coarse_eq_zero (f : JL2) : T (QLeft f) = 0 := by
  change T (JLeft (ALeft f)) = 0
  exact sixColorResidualOperator_leftBoundary_eq_zero H N hN beta hbeta (ALeft f)

/-- Any left-boundary correction leaves the genuine residual operator unchanged. -/
theorem sixColorResidualOperator_sub_coarse (f g : JL2) : T (f - QLeft g) = T f := by
  rw [map_sub, sixColorResidualOperator_coarse_eq_zero, sub_zero]

/-- Exact profile invariance, not just a comparison estimate. -/
theorem sixColorProfileEnergy_sub_coarse (f g : JL2) : Profile (f - QLeft g) = Profile f := by
  rw [← sixColorResidualOperator_norm_sq, sixColorResidualOperator_sub_coarse,
    sixColorResidualOperator_norm_sq]

/-- The complementary projection on the original joint-L2 carrier. -/
def posteriorLeftCenteredOperator : JL2 →L[ℝ] JL2 := ContinuousLinearMap.id ℝ JL2 - QLeft

local notation "Center" => posteriorLeftCenteredOperator H N hN beta hbeta

/-- Explicit centered vector; no pointwise representative is selected. -/
theorem posteriorLeftCenteredOperator_apply (f : JL2) : Center f = f - QLeft f := rfl

/-- The adjoint construction fixes its own left-boundary image. -/
theorem posteriorCoarse_leftBoundary_fixed (u : VL2) : QLeft (JLeft u) = JLeft u := by
  change JLeft (ALeft (JLeft u)) = JLeft u
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint_comp_left]

/-- Evaluation form of the pre-existing projection idempotence. -/
theorem posteriorCoarse_apply_coarse (f : JL2) : QLeft (QLeft f) = QLeft f := by
  exact congrArg (fun S : JL2 →L[ℝ] JL2 => S f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_idempotent
      H N hN beta hbeta)

/-- Centering removes all left-boundary L2 components, not only BCF anchors. -/
theorem posteriorLeftCenteredOperator_leftBoundary (u : VL2) : Center (JLeft u) = 0 := by
  rw [posteriorLeftCenteredOperator_apply, posteriorCoarse_leftBoundary_fixed, sub_self]

/-- Centering removes the constructed optimal left-boundary component. -/
theorem posteriorLeftCenteredOperator_coarse (f : JL2) : Center (QLeft f) = 0 := by
  rw [posteriorLeftCenteredOperator_apply, posteriorCoarse_apply_coarse, sub_self]

/-- Centering twice has no additional effect. -/
theorem posteriorLeftCenteredOperator_idempotent (f : JL2) : Center (Center f) = Center f := by
  change Center (f - QLeft f) = Center f
  rw [map_sub, posteriorLeftCenteredOperator_coarse, sub_zero]

/-- The original orthogonal projection gives a coefficient-one contraction. -/
theorem posteriorLeftCenteredOperator_norm_le (f : JL2) : ‖Center f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg f)).mp
  change ‖f - QLeft f‖ ^ 2 ≤ ‖f‖ ^ 2
  rw [realHilbertProjection_residual_norm_sq QLeft
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_idempotent H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_inner_symm H N hN beta hbeta)]
  exact sub_le_self _ (sq_nonneg _)

/-- Intrinsic centering preserves the normalized residual operator. -/
theorem sixColorResidualOperator_leftCentered (f : JL2) : T (Center f) = T f :=
  sixColorResidualOperator_sub_coarse H N hN beta hbeta f f

/-- Intrinsic centering preserves the existing profile energy exactly. -/
theorem sixColorProfileEnergy_leftCentered (f : JL2) : Profile (Center f) = Profile f :=
  sixColorProfileEnergy_sub_coarse H N hN beta hbeta f f

/-- An unconditional continuous majorant on the full joint-L2 carrier. -/
theorem sixColorProfileEnergy_le_leftCenteredNormSq (f : JL2) : Profile f ≤ ‖Center f‖ ^ 2 := by
  rw [← sixColorProfileEnergy_leftCentered H N hN beta hbeta f]
  exact sixColorProfileEnergy_le_norm_sq H N hN beta hbeta (Center f)

/-- Pythagorean decomposition of every left-corrected approximation error. -/
theorem leftCenteredError_pythagoras (f g : JL2) (u : VL2) :
    ‖f - g - JLeft u‖ ^ 2 =
      ‖Center (f - g)‖ ^ 2 + ‖QLeft (f - g) - JLeft u‖ ^ 2 := by
  let x : JL2 := f - g
  have hFixed : QLeft (QLeft x - JLeft u) = QLeft x - JLeft u := by
    rw [map_sub, posteriorCoarse_apply_coarse, posteriorCoarse_leftBoundary_fixed]
  have hOrth := realHilbertProjection_defect_inner_eq_zero_of_fixed QLeft
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_inner_symm H N hN beta hbeta)
    x (QLeft x - JLeft u) hFixed
  change ‖x - JLeft u‖ ^ 2 = ‖x - QLeft x‖ ^ 2 + ‖QLeft x - JLeft u‖ ^ 2
  have hSplit : x - JLeft u = (x - QLeft x) + (QLeft x - JLeft u) := by abel
  rw [hSplit, norm_add_sq_real, hOrth]
  ring

/-- The least error is attained by the ACTUAL adjoint correction J_L^*(f-g). -/
theorem leftCenteredError_isLeast (f g : JL2) :
    IsLeast (Set.range (fun u : VL2 => ‖f - g - JLeft u‖)) ‖Center (f - g)‖ := by
  constructor
  · exact ⟨ALeft (f - g), rfl⟩
  · rintro _ ⟨u, rfl⟩
    have h := posteriorLeftCenteredOperator_norm_le H N hN beta hbeta (f - g - JLeft u)
    simpa only [map_sub, posteriorLeftCenteredOperator_leftBoundary, sub_zero] using h

/-- Exact norm-loss formula for the optimal error; all terms are intrinsic L2. -/
theorem leftCenteredError_norm_sq (f g : JL2) :
    ‖Center (f - g)‖ ^ 2 = ‖f - g‖ ^ 2 - ‖ALeft (f - g)‖ ^ 2 := by
  rw [posteriorLeftCenteredOperator_apply, realHilbertProjection_residual_norm_sq QLeft
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_idempotent H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_inner_symm H N hN beta hbeta)]
  change ‖f - g‖ ^ 2 - ‖JLeft (ALeft (f - g))‖ ^ 2 = _
  rw [(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta).norm_map]

/-- Sharp stability needs only the centered, rather than full, discrepancy. -/
theorem sixColorProfileAmplitude_le_leftCenteredError (f g : JL2) :
    Amp f ≤ ‖Center (f - g)‖ + Amp g := by
  simp only [sixColorProfileAmplitude_eq_norm]
  have hSplit : T f = T (Center (f - g)) + T g := by
    rw [sixColorResidualOperator_leftCentered, map_sub, sub_add_cancel]
  calc
    ‖T f‖ = ‖T (Center (f - g)) + T g‖ := congrArg norm hSplit
    _ ≤ ‖T (Center (f - g))‖ + ‖T g‖ := norm_add_le _ _
    _ ≤ ‖Center (f - g)‖ + ‖T g‖ :=
      _root_.add_le_add
        (sixColorResidualOperator_norm_le H N hN beta hbeta (Center (f - g))) (le_refl _)

/-- Explicit scalar majorant using the optimal left-corrected approximation. -/
def leftQuotientMajorant (R : ResponseData) (O : BoundedContinuousFunction Joint ℝ)
    (v : Link → ℝ) (f : JL2) : ℝ :=
  (‖Center (f - BCFRep O)‖ +
    Real.sqrt (OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v))) ^ 2

/-- The majorant is continuous in the original joint-L2 topology. -/
theorem leftQuotientMajorant_continuous (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) :
    Continuous (leftQuotientMajorant H N hN beta hbeta R O v) := by
  unfold leftQuotientMajorant
  fun_prop

/-- The constructed majorant is never worse than the full-error majorant. -/
theorem leftQuotientMajorant_le_bcfApproximationMajorant (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (f : JL2) :
    leftQuotientMajorant H N hN beta hbeta R O v f ≤
      bcfApproximationMajorant H N hN beta hbeta R O v f := by
  unfold leftQuotientMajorant bcfApproximationMajorant
  apply (sq_le_sq₀ (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mpr
  exact _root_.add_le_add (posteriorLeftCenteredOperator_norm_le H N hN beta hbeta _)
    (le_refl _)

/-- Validity follows from the propagated INITIAL variation, not from a final
residual premise. No bounded representative of the test vector f is required. -/
theorem sixColorProfileEnergy_le_leftQuotientMajorant (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e) (f : JL2) :
    Profile f ≤ leftQuotientMajorant H N hN beta hbeta R O v f := by
  have hCore := sixColorProfileEnergy_le_variationOscillationEnergy H N hN beta hbeta R O v hv hV
  have hCoreAmp : Amp (BCFRep O) ≤
      Real.sqrt (OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v)) :=
    Real.sqrt_le_sqrt hCore
  have hAmp := (sixColorProfileAmplitude_le_leftCenteredError H N hN beta hbeta f (BCFRep O)).trans
    (_root_.add_le_add (le_refl ‖Center (f - BCFRep O)‖) hCoreAmp)
  have hSq := (sq_le_sq₀ (Real.sqrt_nonneg (Profile f))
    (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mpr hAmp
  rw [Real.sq_sqrt (sixColorProfileEnergy_nonneg H N hN beta hbeta f)] at hSq
  exact hSq

/-- Exact optimization of the error-correction part at fixed initial variation. -/
theorem leftQuotientMajorant_isLeast (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (f : JL2) :
    IsLeast (Set.range (fun u : VL2 =>
      (‖f - BCFRep O - JLeft u‖ +
        Real.sqrt (OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v))) ^ 2))
      (leftQuotientMajorant H N hN beta hbeta R O v f) := by
  constructor
  · exact ⟨ALeft (f - BCFRep O), rfl⟩
  · rintro _ ⟨u, rfl⟩
    unfold leftQuotientMajorant
    apply (sq_le_sq₀ (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mpr
    exact _root_.add_le_add
      ((leftCenteredError_isLeast H N hN beta hbeta f (BCFRep O)).2 ⟨u, rfl⟩) (le_refl _)

/-- Zero approximation recovers the intrinsic centered norm, not the full norm. -/
theorem leftQuotientMajorant_zero (R : ResponseData) (f : JL2) :
    leftQuotientMajorant H N hN beta hbeta R 0 (fun _ => 0) f = ‖Center f‖ ^ 2 := by
  simp [leftQuotientMajorant, posteriorSixColorVariationProfile, posteriorVariationSchedule_zero,
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF]

/-- Arbitrary left-boundary L2 shifts of the test vector are invisible to this majorant. -/
theorem leftQuotientMajorant_add_leftBoundary (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (f : JL2) (u : VL2) :
    leftQuotientMajorant H N hN beta hbeta R O v (f + JLeft u) =
      leftQuotientMajorant H N hN beta hbeta R O v f := by
  unfold leftQuotientMajorant
  simp only [map_sub, map_add, posteriorLeftCenteredOperator_leftBoundary, add_zero]

/-- The constructed anchored initial profile is usable without any oscillation premise. -/
theorem sixColorProfileEnergy_le_leftQuotientRightAnchoredMajorant (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    Profile f ≤ leftQuotientMajorant H N hN beta hbeta R O
      (rightAnchoredInitialVariation H N O) f := by
  apply sixColorProfileEnergy_le_leftQuotientMajorant H N hN beta hbeta R O
    (rightAnchoredInitialVariation H N O) (rightAnchoredInitialVariation_nonneg H N O)
  intro B e A C _hAgree
  exact rightAnchoredInitialVariation_bound H N O B e A C

/-- Locality-facing estimate with only the centered approximation error. -/
theorem sixColorProfileEnergy_le_of_leftQuotientApproximation (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e)
    (f : JL2) (epsilon amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hApprox : ‖Center (f - BCFRep O)‖ ≤ epsilon)
    (hEnergy : OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) ≤ amplitude ^ 2) :
    Profile f ≤ (epsilon + amplitude) ^ 2 := by
  have hRoot : Real.sqrt
      (OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v)) ≤ amplitude := by
    simpa only [Real.sqrt_sq hAmplitude] using Real.sqrt_le_sqrt hEnergy
  have hSum := _root_.add_le_add hApprox hRoot
  have hSq := (sq_le_sq₀ (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (add_nonneg ((norm_nonneg _).trans hApprox) hAmplitude)).mpr hSum
  exact (sixColorProfileEnergy_le_leftQuotientMajorant H N hN beta hbeta R O v hv hV f).trans hSq

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
