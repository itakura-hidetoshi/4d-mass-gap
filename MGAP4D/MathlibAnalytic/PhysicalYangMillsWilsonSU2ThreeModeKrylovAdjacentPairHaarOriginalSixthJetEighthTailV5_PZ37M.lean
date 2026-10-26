import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSexticRowsV5_PZ37M

/-! # PZ37M — first-order sixth-jet differences and the complete eighth-order tail

Every coefficient comes from PZ37B's original integrated moments. The known
sixth Ward zero is used; the degree-eight through twelve terms are bounded.
-/
namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "J1" => p4Q2PZ37B_originalOneSlabTaylor6 H
local notation "J2" => p4Q2PZ37B_originalTwoSlabTaylor6 H

/-- Actual one-slab boundary-difference coefficients, including 1/6!. -/
def p4Q2PZ37M_originalOneJetCoefficients (A D : Cfg) : Fin 6 → ℝ :=
  ![p4Q2PK_originalOneSlabFirstActionMoment H D-p4Q2PK_originalOneSlabFirstActionMoment H A,
    (p4Q2PK_originalOneSlabSecondActionMoment H D-p4Q2PK_originalOneSlabSecondActionMoment H A)/2,
    (p4Q2PP2_originalOneSlabThirdActionMoment H D-p4Q2PP2_originalOneSlabThirdActionMoment H A)/6,
    (p4Q2PX_originalOneSlabFourthActionMoment H D-p4Q2PX_originalOneSlabFourthActionMoment H A)/24,
    -(p4Q2PZ1_originalOneSlabFifthActionMoment H D-p4Q2PZ1_originalOneSlabFifthActionMoment H A)/120,
    (p4Q2PZ36D_originalOneRaw H 6 D-p4Q2PZ36D_originalOneRaw H 6 A)/720]

/-- Actual interacting two-slab boundary-difference coefficients. -/
def p4Q2PZ37M_originalTwoJetCoefficients (A D : Cfg) : Fin 6 → ℝ :=
  ![p4Q2PK_originalOneSlabFirstActionMoment H D-p4Q2PK_originalOneSlabFirstActionMoment H A,
    ((p4Q2PK_originalOneSlabSecondActionMoment H D-p4Q2PK_originalOneSlabSecondActionMoment H A)+
      2*(p4Q2PK_originalMixedTwoSlabActionMoment H D-p4Q2PK_originalMixedTwoSlabActionMoment H A))/2,
    (p4Q2PP2_originalTwoSlabThirdActionMoment H D-p4Q2PP2_originalTwoSlabThirdActionMoment H A)/6,
    (p4Q2PX_originalTwoSlabFourthActionMoment H D-p4Q2PX_originalTwoSlabFourthActionMoment H A)/24,
    -(p4Q2PZ1_originalTwoSlabFifthActionMoment H D-p4Q2PZ1_originalTwoSlabFifthActionMoment H A)/120,
    (p4Q2PZ36D_originalTwoRaw H 6 D-p4Q2PZ36D_originalTwoRaw H 6 A)/720]

private theorem one_difference (beta : ℝ) (A D : Cfg) :
    J1 beta D-J1 beta A =
      ∑ i : Fin 6, beta^(1+i.val)*p4Q2PZ37M_originalOneJetCoefficients H A D i := by
  simp [Fin.sum_univ_succ, p4Q2PZ37M_originalOneJetCoefficients,
    p4Q2PZ37B_originalOneSlabTaylor6, p4Q2PZ1_originalOneSlabFormalTaylor5,
    p4Q2PX_originalOneSlabFormalTaylor4, p4Q2PP2_originalOneSlabFormalTaylor3,
    p4Q2PK_originalOneSlabFormalTaylor2]
  ring

private theorem two_difference (beta : ℝ) (A D : Cfg) :
    J2 beta D-J2 beta A =
      ∑ i : Fin 6, beta^(1+i.val)*p4Q2PZ37M_originalTwoJetCoefficients H A D i := by
  simp [Fin.sum_univ_succ, p4Q2PZ37M_originalTwoJetCoefficients,
    p4Q2PZ37B_originalTwoSlabTaylor6, p4Q2PZ1_originalTwoSlabFormalTaylor5,
    p4Q2PX_originalTwoSlabFormalTaylor4, p4Q2PP2_originalTwoSlabFormalTaylor3,
    p4Q2PK_originalTwoSlabFormalTaylor2]
  ring

/-- No constant boundary difference survives in the genuine one-slab jet. -/
theorem p4Q2PZ37M_originalOneJet_difference_firstOrder
    (beta : ℝ) (hb : ‖beta‖ ≤ 1) (A D : Cfg) :
    ‖J1 beta D-J1 beta A‖ ≤
      ‖beta‖ * ∑ i : Fin 6, ‖p4Q2PZ37M_originalOneJetCoefficients H A D i‖ := by
  rw [one_difference H beta A D]
  simpa using PZ37MEstimates.polynomial_tail beta hb 1 6
    (p4Q2PZ37M_originalOneJetCoefficients H A D)

/-- The full interacting two-slab jet also has a first-order boundary difference. -/
theorem p4Q2PZ37M_originalTwoJet_difference_firstOrder
    (beta : ℝ) (hb : ‖beta‖ ≤ 1) (A D : Cfg) :
    ‖J2 beta D-J2 beta A‖ ≤
      ‖beta‖ * ∑ i : Fin 6, ‖p4Q2PZ37M_originalTwoJetCoefficients H A D i‖ := by
  rw [two_difference H beta A D]
  simpa using PZ37MEstimates.polynomial_tail beta hb 1 6
    (p4Q2PZ37M_originalTwoJetCoefficients H A D)

/-- All five higher coefficients of the actual degree-six moment determinant. -/
def p4Q2PZ37M_originalJetTailCoefficients (A B C : Cfg) : Fin 5 → ℝ :=
  ![p4Q2PZ37B_originalPhysicalEighthCoefficient H A B C,
    p4Q2PZ37B_originalPhysicalNinthCoefficient H A B C,
    p4Q2PZ37B_originalPhysicalTenthCoefficient H A B C,
    p4Q2PZ37B_originalPhysicalEleventhCoefficient H A B C,
    p4Q2PZ37B_originalPhysicalTwelfthCoefficient H A B C]

/-- Complete jet tail: the physical seventh coefficient includes the genuine sixth moments. -/
theorem p4Q2PZ37M_originalSixthMomentJetMinor_eighthRemainder
    (beta : ℝ) (hb : ‖beta‖ ≤ 1) (A B C : Cfg) :
    ‖(J1 beta B-J1 beta A)*(J2 beta C-J2 beta A)-
      (J1 beta C-J1 beta A)*(J2 beta B-J2 beta A)-
      beta^7*p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C‖ ≤
    ‖beta‖^8 * ∑ i : Fin 5, ‖p4Q2PZ37M_originalJetTailCoefficients H A B C i‖ := by
  rw [p4Q2PZ37B_originalSixthMomentJet_afterUnconditionalWard H beta A B C]
  have heq :
      beta^7*p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C +
      beta^8*p4Q2PZ37B_originalPhysicalEighthCoefficient H A B C +
      beta^9*p4Q2PZ37B_originalPhysicalNinthCoefficient H A B C +
      beta^10*p4Q2PZ37B_originalPhysicalTenthCoefficient H A B C +
      beta^11*p4Q2PZ37B_originalPhysicalEleventhCoefficient H A B C +
      beta^12*p4Q2PZ37B_originalPhysicalTwelfthCoefficient H A B C -
      beta^7*p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      ∑ i : Fin 5, beta^(8+i.val)*p4Q2PZ37M_originalJetTailCoefficients H A B C i := by
    simp [Fin.sum_univ_succ, p4Q2PZ37M_originalJetTailCoefficients]
    ring
  rw [heq]
  exact PZ37MEstimates.polynomial_tail beta hb 8 5
    (p4Q2PZ37M_originalJetTailCoefficients H A B C)
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalOneJet_difference_firstOrder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalTwoJet_difference_firstOrder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalSixthMomentJetMinor_eighthRemainder
