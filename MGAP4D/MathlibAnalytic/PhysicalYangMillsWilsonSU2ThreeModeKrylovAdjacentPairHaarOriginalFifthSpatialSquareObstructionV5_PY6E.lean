import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoCrossingQuadraticWeightV5_PY6D
import Mathlib.Tactic

/-!
# P4-Q2-PY6E — complete physical fifth Wilson coefficient is one true Haar minor

PY6C proves the genuine corrected fifth Ward residual is spatial
affine plus -6*V2(B). PY6D proves the original weighted two-crossing
Haar V2(B)=-3*F(B)+kappa, where
   F(B)=∫ w(A)^2 Cross(A,B)^2 dμ_H(A).

The affine original Wilson terms cancel from the full three-boundary
minor. Hence the LITERAL analytic fifth coefficient proved in PX4 is
exactly 3/4 times the determinant of the true first Wilson moment
and F, for EVERY genuine original spatial SU(2) triple at finite H.

This is a genuinely narrower Ward obstruction with original reference
Haar and all complete Wilson middle-slice interactions preserved,
NOT an assumption or proof of nonzero F determinant, third Hankel
positivity, three-mode independence or mass gap.
No new axiom, sorry/admit, Dobrushin or substitute spectral measure.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY6E_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY6E_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY6E_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY6E_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY6E_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalFifthSpatialSquareMinor
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "R5" => p4Q2PY_originalFifthWardResidual H
local notation "D0" => p4Q2PY6_originalReducedFifthConstant H
local notation "D1" => p4Q2PY6_originalReducedFifthLinear H
local notation "κ" => p4Q2PY6_originalTwoCrossingConstant H
local notation "F" => p4Q2PY6_originalSpatialSquareTwoCrossingHaar H
local notation "C5" => p4Q2PX_originalFifthFourthJetCoefficient H

/-- The sole non-affine original fifth Ward content is the true
spatial-half-SQUARED weighted double-crossing Haar profile F. -/
theorem p4Q2PY6_originalFifthWardResidual_spatialSquare (B : Cfg) :
    R5 B = (D0 - 6 * κ) + D1 * w B + 18 * F B := by
  rw [p4Q2PY6_originalFifthWardResidual_affinePlusTwoCrossing H B,
    p4Q2PY6_originalWeightedTwoCrossingHaar_eq_spatialSquare H B]
  ring

/-- EXACT fifth-order analytic coefficient for the ORIGINAL
fully interacting Wilson three-boundary Haar minor: only the
genuine spatial-square TWO-crossing Haar F(B) survives. -/
theorem p4Q2PY6_originalFifthCoefficient_eq_spatialSquareMinor
    (A B C : Cfg) :
    C5 A B C =
      (3 / 4 : ℝ) *
        ((a B - a A) * (F C - F A) -
          (a C - a A) * (F B - F A)) := by
  have hA := p4Q2PY6_originalFifthWardResidual_spatialSquare H A
  have hB := p4Q2PY6_originalFifthWardResidual_spatialSquare H B
  have hC := p4Q2PY6_originalFifthWardResidual_spatialSquare H C
  have hAB : a B - a A = -(w B - w A) := by
    rw [p4Q2PM_originalFirstMoment_spatialWilson H B,
      p4Q2PM_originalFirstMoment_spatialWilson H A]
    unfold p4Q2PS_originalHalfSpatialAction
    ring
  have hAC : a C - a A = -(w C - w A) := by
    rw [p4Q2PM_originalFirstMoment_spatialWilson H C,
      p4Q2PM_originalFirstMoment_spatialWilson H A]
    unfold p4Q2PS_originalHalfSpatialAction
    ring
  rw [p4Q2PY_originalFifthCoefficient_eq_residualMinor H A B C,
    hA, hB, hC, hAB, hAC]
  ring

/-- The literal original Wilson fifth-order analytic asymptotic
inherits the true spatial-square Ward coefficient, with PX4's
proved SIXTH-order remainder for all genuine finite SU(2) triples. -/
theorem p4Q2PY6_originalLiteralWilsonMinor_spatialSquareFifthCoefficient
    (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
            beta ^ 5 * ((3 / 4 : ℝ) *
              ((a B - a A) * (F C - F A) -
                (a C - a A) * (F B - F A)))‖ ≤
                  K * ‖beta‖ ^ 6 := by
  obtain ⟨K, hK, hRem⟩ :=
    p4Q2PX4_originalLiteralWilsonMinor_fifthCoefficient H A B C
  refine ⟨K, hK, ?_⟩
  intro beta hbeta hsmall
  rw [p4Q2PY6_originalFifthCoefficient_eq_spatialSquareMinor H A B C]
    at hRem
  exact hRem beta hbeta hsmall

end OriginalFifthSpatialSquareMinor
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalFifthWardResidual_spatialSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalFifthCoefficient_eq_spatialSquareMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalLiteralWilsonMinor_spatialSquareFifthCoefficient
