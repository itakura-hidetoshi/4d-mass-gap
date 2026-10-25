import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourEdgeFactorialV5_PZ34
import Mathlib.Tactic

/-!
# P4-Q2-PZ35 — exact Schur-eigenlaw descent gate for original SU(2) Haar

PZ34 proved the original four-edge-covered spatial Wilson Haar moment
is 24 times one actual four-link SU(2) Haar integral per plaquette.

The proposed **analytic** SU(2) fundamental Schur computation is
  J_p(B) = (1 / 256) * chi_p(B).
This file does NOT postulate or claim to have proved that integral.
Instead it isolates that still-open genuine compact-SU(2) Haar identity
as a plainly visible theorem hypothesis, and proves its exact, physical
consequences with no substitute model or independent posterior.

For ANY fixed real eigenvalue lambda shared by all original
plaquettes and periods, J_p=lambda*chi_p implies:
  S4(B) = 24 lambda * (number_of_original_plaquettes - 2 w(B)),
  D14(B) = -24 lambda * (w(B)-w(identity)),
  W6(A,B,C) = the ORIGINAL low-sector sixth Ward baseline.
In particular lambda=1/256 predicts the exact affine coefficients
3/32 and -3/32, with no claim that the missing Schur premise is solved.

The proof uses only the imported genuine PZ34 Haar identities, the
original spatial Wilson action, and real ring algebra. No axiom, sorry,
admit, native_decide, altered Wilson model, Dobrushin shortcut or
unjustified rank3/mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ35_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalSchurEigenlawDescent
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "J" => p4Q2PZ34_originalCanonicalFourCrossingHaar H
local notation "S4" => p4Q2PZ32_originalCoveredFourthSupportSum H
local notation "D14" => p4Q2PZ24_originalCenteredFirstFourthDefect H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H
local notation "Low6" => p4Q2PZ32_originalSixthWardLowBaseline H
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- An explicitly UNPROVED pointwise compact-SU(2) Schur eigenlaw
for the true normalized-Haar four-link integral. This is a predicate,
not an additional axiom, not an alternate model, and not an asserted
fact. PZ35 descent theorems below all visibly require its proof. -/
def p4Q2PZ35_originalFourHaarSchurEigenlaw (lambda : ℝ) : Prop :=
  ∀ (p : Plaq) (B : Cfg), J p B = lambda * χ p B

/-- The original complete spatial Wilson character sum is exactly
number of original plaquettes minus twice the ORIGINAL half-action. -/
theorem p4Q2PZ35_originalTraceSum_eq_card_sub_twoHalfAction (B : Cfg) :
    (∑ p : Plaq, χ p B) =
      (Fintype.card Plaq : ℝ) - 2 * w B := by
  change p4Q2PW2_originalAllPlaquetteRealTrace H B =
    (Fintype.card Plaq : ℝ) -
      2 * p4Q2PS_originalHalfSpatialAction H B
  unfold p4Q2PS_originalHalfSpatialAction
  rw [p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum H B]
  ring

/-- A *proved conditional descent*: one common genuine SU(2)
four-link Schur eigenvalue makes the exact PZ34 24-fold support
AFFINE in the physical spatial Wilson half-action. -/
theorem p4Q2PZ35_originalS4_affine_of_SchurEigenlaw
    (lambda : ℝ)
    (hSchur : p4Q2PZ35_originalFourHaarSchurEigenlaw H lambda)
    (B : Cfg) :
    S4 B =
      24 * lambda * ((Fintype.card Plaq : ℝ) - 2 * w B) := by
  classical
  calc
    S4 B = 24 * ∑ p : Plaq, J p B :=
      p4Q2PZ34_originalS4_eq_twentyFourCanonicalHaar H B
    _ = 24 * ∑ p : Plaq, lambda * χ p B := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _hp
      exact hSchur p B
    _ = 24 * (lambda * (∑ p : Plaq, χ p B)) := by
      rw [← Finset.mul_sum]
    _ = 24 * lambda * (∑ p : Plaq, χ p B) := by ring
    _ = 24 * lambda *
          ((Fintype.card Plaq : ℝ) - 2 * w B) := by
      rw [p4Q2PZ35_originalTraceSum_eq_card_sub_twoHalfAction H B]

/-- The ORIGINAL centered D14 is then affine, with its constant
correctly fixed by the true identity boundary, without assuming
w(identity)=0 or changing the physical boundary normalization. -/
theorem p4Q2PZ35_originalD14_linearDifference_of_SchurEigenlaw
    (lambda : ℝ)
    (hSchur : p4Q2PZ35_originalFourHaarSchurEigenlaw H lambda)
    (B : Cfg) :
    D14 B = -24 * lambda * (w B - w I) := by
  rw [p4Q2PZ32_originalD14_eq_coveredFourthSupportDifference H B,
    p4Q2PZ35_originalS4_affine_of_SchurEigenlaw H lambda hSchur B,
    p4Q2PZ35_originalS4_affine_of_SchurEigenlaw H lambda hSchur I]
  ring

/-- The TRUE sixth Ward FOUR-EDGE correction would vanish under
the one missing SU(2) Haar eigenlaw, leaving exactly the previously
proved physical low-sector baseline (which need not vanish). -/
theorem p4Q2PZ35_originalSixthWard_eq_lowBaseline_of_SchurEigenlaw
    (lambda : ℝ)
    (hSchur : p4Q2PZ35_originalFourHaarSchurEigenlaw H lambda)
    (A B C : Cfg) :
    W6 A B C = Low6 A B C := by
  apply p4Q2PZ32_originalSixthWard_lowOnly_of_affineFourthSupport H
    (-48 * lambda) (24 * lambda * (Fintype.card Plaq : ℝ))
  intro D
  rw [p4Q2PZ35_originalS4_affine_of_SchurEigenlaw H lambda hSchur D]
  ring

/-- The explicit SU(2) fundamental-representation coefficient
predicted analytically by FOUR applications of -1/4 Schur
orthogonality. This result REMAINS CONDITIONAL until its
genuine Haar integral premise is established in Lean. -/
theorem p4Q2PZ35_originalS4_threeOverThirtyTwo_of_SchurQuarter
    (hSchur :
      p4Q2PZ35_originalFourHaarSchurEigenlaw H (1 / 256 : ℝ))
    (B : Cfg) :
    S4 B = (3 / 32 : ℝ) *
      ((Fintype.card Plaq : ℝ) - 2 * w B) := by
  rw [p4Q2PZ35_originalS4_affine_of_SchurEigenlaw H
    (1 / 256 : ℝ) hSchur B]
  ring

theorem p4Q2PZ35_originalD14_threeOverThirtyTwo_of_SchurQuarter
    (hSchur :
      p4Q2PZ35_originalFourHaarSchurEigenlaw H (1 / 256 : ℝ))
    (B : Cfg) :
    D14 B = -(3 / 32 : ℝ) * (w B - w I) := by
  rw [p4Q2PZ35_originalD14_linearDifference_of_SchurEigenlaw H
    (1 / 256 : ℝ) hSchur B]
  ring

theorem p4Q2PZ35_originalSixthWard_eq_lowBaseline_of_SchurQuarter
    (hSchur :
      p4Q2PZ35_originalFourHaarSchurEigenlaw H (1 / 256 : ℝ))
    (A B C : Cfg) :
    W6 A B C = Low6 A B C :=
  p4Q2PZ35_originalSixthWard_eq_lowBaseline_of_SchurEigenlaw
    H (1 / 256 : ℝ) hSchur A B C

/-- A verified converse obstruction: a genuine sixth Ward
correction away from Low6 disproves EVERY common Schur scalar.
The antecedent is not asserted or postulated. -/
theorem p4Q2PZ35_originalNonlowWard_forces_noSchurEigenlaw
    (A B C : Cfg)
    (hResidual : W6 A B C ≠ Low6 A B C)
    (lambda : ℝ) :
    ¬ p4Q2PZ35_originalFourHaarSchurEigenlaw H lambda := by
  intro hSchur
  exact hResidual
    (p4Q2PZ35_originalSixthWard_eq_lowBaseline_of_SchurEigenlaw
      H lambda hSchur A B C)

end OriginalSchurEigenlawDescent
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalTraceSum_eq_card_sub_twoHalfAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalS4_affine_of_SchurEigenlaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalD14_linearDifference_of_SchurEigenlaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalSixthWard_eq_lowBaseline_of_SchurEigenlaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalS4_threeOverThirtyTwo_of_SchurQuarter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalD14_threeOverThirtyTwo_of_SchurQuarter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalSixthWard_eq_lowBaseline_of_SchurQuarter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35_originalNonlowWard_forces_noSchurEigenlaw
