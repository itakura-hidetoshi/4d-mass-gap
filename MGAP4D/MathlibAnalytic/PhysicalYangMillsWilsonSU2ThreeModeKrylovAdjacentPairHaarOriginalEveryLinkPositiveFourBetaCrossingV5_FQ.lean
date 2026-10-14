import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalWilsonCrossRatioV5_FP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarConcretePositiveBetaCrossingWitness
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion
import Mathlib.Tactic

/-!
# P4-Q2-FQ: every physical spatial link has an exact 4*beta Wilson crossing

FP proves that the TRUE continuous physical vacuum conditional right-link
log-weight has a mixed left/right four-corner difference equal EXACTLY to
the temporal Wilson one-link energy cross difference. The off-link kernel
coefficient, right spatial half action and actual physical Perron vacuum
all cancel without introducing a surrogate conditional law.

Previously the full physical crossing witness was constructed at only the
distinguished time-zero spatial link. Here the explicit SU(2) pi rotation
witness is constructed at EVERY original physical spatial link e, for
EVERY even-periodic finite-volume H (including H=0).

Choose left_1(e)=1, left_2(e)=R(pi), right insertion g=1 and h=R(pi).
Since E_W(1)=0 and E_W(R(pi))=E_W(R(pi)^(-1))=2, the actual conditional
four-corner LOG crossing difference is exactly 4*beta at EVERY e and
for every unchanged physical right-boundary background B:

   crossLog_Wilson(H,e,B,beta) = 4*beta.

It is strictly positive for beta>0. The result is a quantitative,
volume-independent, ORIGINAL Wilson-kernel nonseparability witness;
it is NOT yet a quantitative lower bound on the INTEGRATED original
physical conditional RMS, much less a continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

namespace GroundStatePosteriorJoint

/-- The ORIGINAL SU(2) identity left boundary with ONLY the chosen
physical link e rotated by pi. The link is arbitrary, not the fixed
distinguished spatial edge from the earlier concrete witness. -/
noncomputable def p4Q2FQ_originalSU2LeftPiRotationAtLink
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  Function.update
    (originalWilsonExplicitIdentityBoundary H) e
    (specialUnitaryTwoRotation Real.pi)

theorem p4Q2FQ_originalSU2LeftPiRotationAtLink_value
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FQ_originalSU2LeftPiRotationAtLink H e e =
      specialUnitaryTwoRotation Real.pi := by
  simp [p4Q2FQ_originalSU2LeftPiRotationAtLink]

/-- The exact original physical posterior logarithmic four-corner
crossing at an arbitrary physical SU(2) link, using two genuinely
different left physical boundaries and two genuine inserted values. -/
noncomputable def p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e 1 -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H 2 (by norm_num) beta hbeta (originalWilsonExplicitIdentityBoundary H) right e
      (specialUnitaryTwoRotation Real.pi)) -
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e 1 -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
      H 2 (by norm_num) beta hbeta (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
      (specialUnitaryTwoRotation Real.pi))

/-- An EXACT nonzero quantitative crossing witness for EVERY original
physical spatial link: no volume-dependent constant or unproved
full-configuration translation invariance is needed. -/
theorem p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing_eq_four_beta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing H beta hbeta right e =
      4 * beta := by
  let R : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    specialUnitaryTwoRotation Real.pi
  let A := originalWilsonExplicitIdentityBoundary H
  let A' := p4Q2FQ_originalSU2LeftPiRotationAtLink H e
  have hAtA : A e = (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := rfl
  have hAtA' : A' e = R :=
    p4Q2FQ_originalSU2LeftPiRotationAtLink_value H e
  have hZero :
      specialUnitaryWilsonPlaquetteEnergy 2
        (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) = 0 :=
    specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)
  have hPi :
      specialUnitaryWilsonPlaquetteEnergy 2 R = 2 :=
    originalWilsonExplicitPiRotation_energy_eq_two
  have hPiInv :
      specialUnitaryWilsonPlaquetteEnergy 2 R⁻¹ = 2 := by
    rw [specialUnitaryWilsonPlaquetteEnergy_inv]
    exact hPi
  unfold p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing
  change
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H 2 (by norm_num) beta hbeta A right e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H 2 (by norm_num) beta hbeta A right e R) -
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H 2 (by norm_num) beta hbeta A' right e (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight
        H 2 (by norm_num) beta hbeta A' right e R) = 4 * beta
  rw [p4Q2FP_actualWilsonCompleteFiberLog_crossDifference_eq_temporalEnergy
    H 2 (by norm_num) beta hbeta A A' right e
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) R]
  rw [hAtA, hAtA']
  simp only [inv_one, one_mul, mul_one, inv_mul_cancel]
  rw [hZero, hPi, hPiInv]
  ring

/-- Every actual SU(2) spatial link has a strictly nonzero conditional
four-corner crossing at every positive Wilson coupling. Quantitative
crossLog=4*beta is stronger than a mere existential witness, but does
not alone imply a uniform integrated RMS floor. -/
theorem p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing
      H beta (le_of_lt hbeta) right e := by
  rw [p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing_eq_four_beta]
  linarith

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FQ_originalSU2LeftPiRotationAtLink_value
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing_eq_four_beta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FQ_originalSU2WilsonEveryLinkFourCornerLogCrossing_pos
