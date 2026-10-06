import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSixColorPrefixMajorant
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Sharp L2-stable majorants from posterior BCF approximations

The genuine six-color stage residuals form a single linear map into a finite
Hilbert product. Scaling by sqrt(1/6) makes its squared norm EXACTLY the
pre-existing profile energy. Pythagorean path loss makes this map a contraction;
there is no spatial-cardinality factor and no commutativity premise.

Consequently, for any joint-L2 vector f and any joint BCF O with an INITIAL
variation profile v, the propagated posterior energy E_v from PR #5215 gives

  Profile(f) <= (||f - iota O|| + sqrt(E_v))^2.

The displayed right side is an explicitly constructed continuous scalar
function of f. Its continuity is not a new hypothesis, and neither a bounded
representative of f nor L2-continuity of the pointwise variation is required.

This does NOT construct a support-distance-small approximation or variation
energy. Those two quantitative model estimates remain the locality frontier.
It does not assert that the majorant dominates the pointwise oscillation energy
of every BCF: it dominates the genuine profile directly. Physicality and physical
transfer/reconstruction compatibility remain separate, and both no-go boundaries
are unchanged.
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
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "LocalProfile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy H
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "ResidualFamily" => PiLp 2 (fun _ : Link => JL2)

/-- The actual canonical local amplitude, now on every joint-L2 vector. -/
theorem sixColorLocalProfile_eq_residualNorm (f : JL2) (e : Link) :
    LocalProfile f e =
      ‖realHilbertProjectionSweep PJoint (posteriorSixColorPrefixLinks H e) f -
        PJoint e (realHilbertProjectionSweep PJoint (posteriorSixColorPrefixLinks H e) f)‖ := by
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
      H N hN beta hbeta e
      (posteriorFixedColorPrefix H (periodicHypercubicEvenSpatialSliceLinkColor H e) ⟨e, rfl⟩)
      (posteriorFixedColorSuffix H (periodicHypercubicEvenSpatialSliceLinkColor H e) ⟨e, rfl⟩)
      f (posteriorFixedColorPrefix_split H _ _) (posteriorFixedColorPrefix_fresh H _ _)
  simpa only [posteriorSixColorPrefixLinks, fixedColorStage_eq_projectionSchedule,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2]
    using hLocal

/-- The normalized residual family is linear; it retains every actual prefix. -/
def sixColorResidualLinearMap : JL2 →ₗ[ℝ] ResidualFamily :=
  (Real.sqrt (1 / 6 : ℝ)) •
    ((WithLp.linearEquiv 2 ℝ (Link → JL2)).symm.toLinearMap.comp
      (LinearMap.pi fun e =>
        ((ContinuousLinearMap.id ℝ JL2 - PJoint e).comp
          (realHilbertProjectionSweep PJoint (posteriorSixColorPrefixLinks H e))).toLinearMap))

/-- Concrete evaluation of the bundled residuals. -/
theorem sixColorResidualLinearMap_apply (f : JL2) :
    sixColorResidualLinearMap H N hN beta hbeta f =
      Real.sqrt (1 / 6 : ℝ) • WithLp.toLp 2 (fun e : Link =>
        realHilbertProjectionSweep PJoint (posteriorSixColorPrefixLinks H e) f -
          PJoint e (realHilbertProjectionSweep PJoint (posteriorSixColorPrefixLinks H e) f)) := rfl

/-- Exact normalization: no extra comparison coefficient or link count. -/
theorem sixColorResidualLinearMap_norm_sq (f : JL2) :
    ‖sixColorResidualLinearMap H N hN beta hbeta f‖ ^ 2 = Profile f := by
  rw [sixColorResidualLinearMap_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 6), PiLp.norm_sq_eq_of_L2]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
  congr 1
  exact Finset.sum_congr rfl fun e _ =>
    (congrArg (fun t : ℝ => t ^ 2)
      (sixColorLocalProfile_eq_residualNorm H N hN beta hbeta f e)).symm

private theorem fixedColorPathLoss_le_norm_sq
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
      H N hN beta hbeta color f ≤ ‖f‖ ^ 2 := by
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
    H N hN beta hbeta color
  let cs := (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList
  have hLoss := realHilbertProjectionSweep_norm_sq_loss P
    (fun e =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta e.1)
    (fun e x y =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e.1 x y) cs f
  change realHilbertProjectionSweepPathLoss P cs f ≤ ‖f‖ ^ 2
  rw [← hLoss]
  exact sub_le_self _ (sq_nonneg _)

/-- All six color sweeps start at the same vector and lose at most its energy. -/
theorem sixColorProfileEnergy_le_norm_sq (f : JL2) : Profile f ≤ ‖f‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_eq_pathLoss]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
  calc
    _ ≤ (1 / 6 : ℝ) * ∑ _c : Fin 6, ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun c _ =>
          fixedColorPathLoss_le_norm_sq H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)
        (by norm_num)
    _ = ‖f‖ ^ 2 := by norm_num [Finset.sum_const]; ring

/-- A volume-independent norm bound, not a positive spectral-gap claim. -/
theorem sixColorResidualLinearMap_norm_le (f : JL2) :
    ‖sixColorResidualLinearMap H N hN beta hbeta f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg f)).mp
  rw [sixColorResidualLinearMap_norm_sq]
  exact sixColorProfileEnergy_le_norm_sq H N hN beta hbeta f

/-- The genuine residual family as a bounded linear operator. -/
def sixColorResidualOperator : JL2 →L[ℝ] ResidualFamily :=
  (sixColorResidualLinearMap H N hN beta hbeta).mkContinuous 1
    (fun f => by simpa only [one_mul] using
      sixColorResidualLinearMap_norm_le H N hN beta hbeta f)

/-- Bundling continuity does not change the exact profile energy. -/
theorem sixColorResidualOperator_norm_sq (f : JL2) :
    ‖sixColorResidualOperator H N hN beta hbeta f‖ ^ 2 = Profile f :=
  sixColorResidualLinearMap_norm_sq H N hN beta hbeta f

/-- The bundled operator is norm-contracting. -/
theorem sixColorResidualOperator_norm_le (f : JL2) :
    ‖sixColorResidualOperator H N hN beta hbeta f‖ ≤ ‖f‖ :=
  sixColorResidualLinearMap_norm_le H N hN beta hbeta f

/-- Nonnegativity on the whole original Hilbert carrier. -/
theorem sixColorProfileEnergy_nonneg (f : JL2) : 0 ≤ Profile f := by
  rw [← sixColorResidualOperator_norm_sq]
  exact sq_nonneg _

/-- The existing normalized profile amplitude, without representative choices. -/
def sixColorProfileAmplitude (f : JL2) : ℝ := Real.sqrt (Profile f)

/-- The amplitude is the norm of the normalized residual operator. -/
theorem sixColorProfileAmplitude_eq_norm (f : JL2) :
    sixColorProfileAmplitude H N hN beta hbeta f =
      ‖sixColorResidualOperator H N hN beta hbeta f‖ := by
  unfold sixColorProfileAmplitude
  rw [← sixColorResidualOperator_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Sharp approximation stability with coefficient one on the L2 error. -/
theorem sixColorProfileAmplitude_le_add (f g : JL2) :
    sixColorProfileAmplitude H N hN beta hbeta f ≤
      ‖f - g‖ + sixColorProfileAmplitude H N hN beta hbeta g := by
  let T := sixColorResidualOperator H N hN beta hbeta
  simp only [sixColorProfileAmplitude_eq_norm]
  calc
    ‖T f‖ = ‖T (f - g) + T g‖ := by rw [← map_add, sub_add_cancel]
    _ ≤ ‖T (f - g)‖ + ‖T g‖ := norm_add_le _ _
    _ ≤ ‖f - g‖ + ‖T g‖ :=
      _root_.add_le_add
        (sixColorResidualOperator_norm_le H N hN beta hbeta (f - g))
        (le_refl ‖T g‖)

/-- The square root of the genuine profile is 1-Lipschitz uniformly in volume. -/
theorem sixColorProfileAmplitude_lipschitz :
    LipschitzWith 1 (sixColorProfileAmplitude H N hN beta hbeta) := by
  apply LipschitzWith.of_le_add
  intro f g
  simpa only [dist_eq_norm, add_comm] using
    sixColorProfileAmplitude_le_add H N hN beta hbeta f g

/-- The nonnegative propagated energy for any initial real profile. -/
theorem posteriorSixColorVariationEnergy_nonneg (R : ResponseData) (v : Link → ℝ) :
    0 ≤ OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) := by
  unfold periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ => sq_nonneg _)

/-- An explicit continuous majorant from a single BCF approximation and its
propagated initial-variation energy. Validity is proved below, not assumed. -/
def bcfApproximationMajorant (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (f : JL2) : ℝ :=
  (‖f - BCFRep O‖ +
    Real.sqrt (OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v))) ^ 2

/-- Continuity is automatic for fixed approximation data; no pointwise
oscillation map is asserted to be L2-continuous. -/
theorem bcfApproximationMajorant_continuous (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) :
    Continuous (bcfApproximationMajorant H N hN beta hbeta R O v) := by
  unfold bcfApproximationMajorant
  fun_prop

/-- At its BCF center the majorant recovers exactly the PR #5215 energy. -/
theorem bcfApproximationMajorant_at_representative (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) :
    bcfApproximationMajorant H N hN beta hbeta R O v (BCFRep O) =
      OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) := by
  simp only [bcfApproximationMajorant, sub_self, norm_zero, zero_add]
  exact Real.sq_sqrt (posteriorSixColorVariationEnergy_nonneg H N hN beta hbeta R v)

/-- A genuine full-L2 scalar bound constructed solely from INITIAL BCF variation.
The test vector f is arbitrary and needs no bounded representative. -/
theorem sixColorProfileEnergy_le_bcfApproximationMajorant (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e) (f : JL2) :
    Profile f ≤ bcfApproximationMajorant H N hN beta hbeta R O v f := by
  have hCore := sixColorProfileEnergy_le_variationOscillationEnergy
    H N hN beta hbeta R O v hv hV
  have hCoreAmp : sixColorProfileAmplitude H N hN beta hbeta (BCFRep O) ≤
      Real.sqrt (OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v)) :=
    Real.sqrt_le_sqrt hCore
  have hAmp := (sixColorProfileAmplitude_le_add H N hN beta hbeta f (BCFRep O)).trans
    (_root_.add_le_add (le_refl ‖f - BCFRep O‖) hCoreAmp)
  have hSq := (sq_le_sq₀ (Real.sqrt_nonneg (Profile f))
    (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mpr hAmp
  rw [Real.sq_sqrt (sixColorProfileEnergy_nonneg H N hN beta hbeta f)] at hSq
  exact hSq

/-- Quantitative locality-facing form: separate L2 approximation error and
propagated variation amplitude. Neither premise is a final profile bound. -/
theorem sixColorProfileEnergy_le_of_bcfApproximation (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e)
    (f : JL2) (epsilon amplitude : ℝ) (hAmplitude : 0 ≤ amplitude)
    (hApprox : ‖f - BCFRep O‖ ≤ epsilon)
    (hEnergy : OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v) ≤
      amplitude ^ 2) :
    Profile f ≤ (epsilon + amplitude) ^ 2 := by
  have hRoot : Real.sqrt
      (OscEnergy (posteriorSixColorVariationProfile H N hN beta hbeta R v)) ≤ amplitude := by
    simpa only [Real.sqrt_sq hAmplitude] using Real.sqrt_le_sqrt hEnergy
  have hSum := add_le_add hApprox hRoot
  have hSquare := (sq_le_sq₀
    (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (add_nonneg ((norm_nonneg _).trans hApprox) hAmplitude)).mpr hSum
  exact (sixColorProfileEnergy_le_bcfApproximationMajorant
    H N hN beta hbeta R O v hv hV f).trans hSquare

/-- Canonical half-barrier specialization, still valid on the entire joint L2. -/
theorem sixColorProfileEnergy_le_canonicalBCFApproximationMajorant
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (O : BoundedContinuousFunction Joint ℝ) (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e)
    (hV : ∀ (B : Cfg) (e : Link) (A C : Cfg),
      Agree A C e → |O (B, A) - O (B, C)| ≤ v e) (f : JL2) :
    Profile f ≤ (‖f - BCFRep O‖ +
      Real.sqrt (OscEnergy (canonicalPosteriorSixColorVariation H N hN beta hbeta s hs hcut v))) ^ 2 :=
  sixColorProfileEnergy_le_bcfApproximationMajorant H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      H N hN s hs beta hbeta hcut) O v hv hV f

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
