import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEveryLinkPositiveFourBetaCrossingV5_FQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalNormalizedPosteriorTemporalLogCrossingV5_FR
import Mathlib.Tactic

/-!
# P4-Q2-FS: real normalized Wilson posterior depends on left SU(2) link at every e

FQ proves for EVERY physical spatial link e that the ORIGINAL continuous
Wilson kernel/vacuum complete-fiber four-corner log cross difference is
EXACTLY 4*beta, using identity and pi-rotated original left configurations.

FR independently proves that the four-corner log difference of the
GENUINE *normalized* Wilson conditional posterior density is IDENTICAL
to the Wilson kernel log crossing: all true partition functions cancel.

Here compose FQ+FR with NO replacement of posterior by Haar:

  (log p(A0,1)-log p(A0,Rpi))
    - (log p(Ae,1)-log p(Ae,Rpi)) = 4*beta.

For beta>0 this is strict at EVERY actual spatial link e and every
right-boundary background. Consequently the true normalized posterior
density at the two original left boundaries must differ at at least
one of the two explicit right values 1, R(pi).

This shows pointwise nontriviality and left-link sensitivity of
the actual interacting conditional law, not a lower bound on the
integrated genuine physical source-dependent RMS, nor a claim of
volume-uniform summability or 4D continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

namespace GroundStatePosteriorJoint

/-- The original SU(2) posterior at an arbitrary physical link, evaluated
at two real left boundaries and two explicit right link values. -/
noncomputable def p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (Real.log
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e 1) -
    Real.log
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e
        (specialUnitaryTwoRotation Real.pi))) -
  (Real.log
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e 1) -
    Real.log
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
        (specialUnitaryTwoRotation Real.pi)))

/-- Every original physical SU(2) one-link posterior-normalized log
crossing is EXACTLY 4 beta for ALL finite volumes H and link e. -/
theorem p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog_eq_four_beta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog
      H beta hbeta right e = 4 * beta := by
  let A := originalWilsonExplicitIdentityBoundary H
  let A' := p4Q2FQ_originalSU2LeftPiRotationAtLink H e
  let R : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    specialUnitaryTwoRotation Real.pi
  have hFQ :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H 2 (by norm_num) beta hbeta A right e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H 2 (by norm_num) beta hbeta A right e R) -
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H 2 (by norm_num) beta hbeta A' right e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
          H 2 (by norm_num) beta hbeta A' right e R) = 4 * beta := by
    exact p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing_eq_four_beta
      H beta hbeta right e
  have hEnergy :
      -beta *
        ((specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) -
            specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * R)) -
          (specialUnitaryWilsonPlaquetteEnergy 2 ((A' e)⁻¹ * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) -
            specialUnitaryWilsonPlaquetteEnergy 2 ((A' e)⁻¹ * R))) = 4 * beta := by
    rw [p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporalEnergy
      H 2 (by norm_num) beta hbeta A A' right e
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) R] at hFQ
    exact hFQ
  unfold p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog
  change
    (Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H 2 (by norm_num) beta hbeta A right e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) -
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H 2 (by norm_num) beta hbeta A right e R)) -
    (Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H 2 (by norm_num) beta hbeta A' right e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) -
      Real.log
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
          H 2 (by norm_num) beta hbeta A' right e R)) = 4 * beta
  rw [p4Q2FR_originalWilsonNormalizedPosteriorLogCrossing_eq_temporalEnergy
    H 2 (by norm_num) beta hbeta A A' right e
    (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) R]
  exact hEnergy

/-- Original interacting Wilson posterior normalized densities at two
explicit left-boundary configurations cannot simultaneously coincide at
both distinct right-target SU(2) values for positive beta. The witness
exists for EVERY physical link, not just one selected link. -/
theorem p4Q2FS_originalSU2EveryLinkTruePosteriorDensity_leftSensitive
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (originalWilsonExplicitIdentityBoundary H) right e 1 ≠
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e 1 ∨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (originalWilsonExplicitIdentityBoundary H) right e
        (specialUnitaryTwoRotation Real.pi) ≠
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
        (specialUnitaryTwoRotation Real.pi) := by
  have hPositive : 0 <
      p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog
        H beta (le_of_lt hbeta) right e := by
    rw [p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog_eq_four_beta]
    linarith
  by_contra hNo
  push Not at hNo
  obtain ⟨hOne, hRot⟩ := hNo
  have hZero :
      p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog
        H beta (le_of_lt hbeta) right e = 0 := by
    unfold p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog
    rw [hOne, hRot]
    ring
  exact (ne_of_gt hPositive) hZero

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FS_originalSU2WilsonEveryLinkPosteriorCrossLog_eq_four_beta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FS_originalSU2EveryLinkTruePosteriorDensity_leftSensitive
