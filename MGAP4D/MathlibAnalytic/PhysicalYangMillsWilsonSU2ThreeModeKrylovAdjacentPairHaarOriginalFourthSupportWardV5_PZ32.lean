import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAllPeriodsCubicCancellationV5_PZ31B
import Mathlib.Tactic

/-!
# P4-Q2-PZ32 — exact original sixth Ward reduction after all-period D32 cancellation

PZ31B (#5896) establishes that the TRUE original SU(2) spatial-cubic
two-temporal-crossing Haar term and its boundary defect vanish at
EVERY finite even spatial period, including period two (H=0).

This module TRANSPORTS that physical Haar result into PZ24's true
sixth Ward/Vandermonde identity and PZ25's EXACT four-edge-covering
Haar selection. Consequently the only unselected fifth mixed-potential
boundary defect is D14, itself an explicit sum over the genuinely
four-edge-covering temporal crossing quadruples. No crossing link or
intermediate spatial plaquette is discarded without a proven Haar zero.

The optional affine-support implication is explicitly CONDITIONAL:
SU(2) character orthogonality has NOT yet shown that the true
four-crossing support sum is affine in the original spatial Wilson
action. No W6 nonzero witness, third Hankel positivity, rank3,
U0, endpoint E, continuum mass gap, new axiom, sorry, admit,
Dobrushin approximation or replacement posterior is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ32_plaquetteFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalAllPeriodsFourthSupportWard
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "I" => (fun _ : Link =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Profile" => p4Q2PZ23_originalLowWardBoundaryProfile H
local notation "Shape" => p4Q2PZ24_originalLowWardSymmetricQuadratic H
local notation "F32" => p4Q2PZ22_originalSpatialCubeCrossingSquareHaar H
local notation "F23" => p4Q2PZ22_originalSpatialSquareCrossingCubeHaar H
local notation "F14" => p4Q2PZ22_originalSpatialCrossingFourthHaar H
local notation "V" => p4Q2PZ21_originalMixedFifthBoundaryPotential H
local notation "D14" => p4Q2PZ24_originalCenteredFirstFourthDefect H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H

/-- The genuine original spatial-cubic/crossing-square mixed sector
has exactly the SAME value at every spatial boundary configuration,
not merely at the nonminimal even periods. -/
theorem p4Q2PZ32_originalF32_Haar_boundaryInvariant (B : Cfg) :
    F32 B = F32 I := by
  rw [p4Q2PZ24_originalF32_eq_const_sub_defect H B,
    p4Q2PZ31B_originalAllPeriodsCenteredCubicDefect_zero H B]
  ring

/-- Exact fifth mixed potential of the original SU(2) Wilson model:
all genuine nonconstant higher-sector terms except D14 are gone. -/
theorem p4Q2PZ32_originalMixedPotential_onlyFourthDefect (B : Cfg) :
    V B = (Profile (w B) + 70*F32 I + 30*F23 I + 5*F14 I) -
      5*D14 B := by
  rw [p4Q2PZ24_originalMixedPotential_centeredTwoDefects H B,
    p4Q2PZ31B_originalAllPeriodsCenteredCubicDefect_zero H B]
  ring

/-- Two boundaries with equal ORIGINAL spatial Wilson action can
have distinct fifth mixed potential only through the genuine D14. -/
theorem p4Q2PZ32_originalMixedPotential_sameSpatialAction
    (A B : Cfg) (hAB : w A = w B) :
    V B - V A = -5*(D14 B-D14 A) := by
  rw [p4Q2PZ32_originalMixedPotential_onlyFourthDefect H B,
    p4Q2PZ32_originalMixedPotential_onlyFourthDefect H A,
    hAB]
  ring

/-- The exact physically normalized low-sector term in the
original sixth Ward obstruction; no surrogate Vandermonde. -/
noncomputable def p4Q2PZ32_originalSixthWardLowBaseline
    (A B C : Cfg) : ℝ :=
  720*C6 A B C +
    6*(w B-w A)*(w C-w A)*(w C-w B)*
      Shape (w A) (w B) (w C)

local notation "Low6" => p4Q2PZ32_originalSixthWardLowBaseline H

/-- UNCONDITIONAL finite-volume Ward identity after PZ31B:
D32 is identically zero for every even period, leaving the one
genuine fourth-crossing/first-spatial Haar defect D14. -/
theorem p4Q2PZ32_originalSixthWard_onlyFourthDefect
    (A B C : Cfg) :
    W6 A B C = Low6 A B C -
      30*((w B-w A)*(D14 C-D14 A) -
          (w C-w A)*(D14 B-D14 A)) := by
  rw [p4Q2PZ24_originalSixthWard_centeredVandermonde H A B C,
    p4Q2PZ31B_originalAllPeriodsCenteredCubicDefect_zero H A,
    p4Q2PZ31B_originalAllPeriodsCenteredCubicDefect_zero H B,
    p4Q2PZ31B_originalAllPeriodsCenteredCubicDefect_zero H C]
  unfold p4Q2PZ32_originalSixthWardLowBaseline
  ring

/-- The EXACT remaining fourth-crossing contribution on the true
periodic SU(2) spatial slice. Only tuples covering all four genuine
edges of the associated plaquette are present, as PROVED by PZ25. -/
noncomputable def p4Q2PZ32_originalCoveredFourthSupportSum (B : Cfg) : ℝ :=
  ∑ p : Plaq, p4Q2PZ25_originalCoveredPlaquetteFourthHaar H p B

local notation "S4" => p4Q2PZ32_originalCoveredFourthSupportSum H

/-- The complete original D14 boundary defect is one half the
boundary difference of actual four-edge-covering Haar sums. -/
theorem p4Q2PZ32_originalD14_eq_coveredFourthSupportDifference
    (B : Cfg) :
    D14 B = (1/2 : ℝ) * (S4 B-S4 I) := by
  simpa only [p4Q2PZ32_originalCoveredFourthSupportSum] using
    (p4Q2PZ25_originalFourthDefect_onlyCovered H B)

/-- PZ32 physical sixth Ward obstruction in terms of ONLY true
four-edge-covering Haar quadruples; 30 × 1/2 = 15 exactly. -/
theorem p4Q2PZ32_originalSixthWard_onlyCoveredFourthSupport
    (A B C : Cfg) :
    W6 A B C = Low6 A B C -
      15*((w B-w A)*(S4 C-S4 A) -
          (w C-w A)*(S4 B-S4 A)) := by
  rw [p4Q2PZ32_originalSixthWard_onlyFourthDefect H A B C,
    p4Q2PZ32_originalD14_eq_coveredFourthSupportDifference H A,
    p4Q2PZ32_originalD14_eq_coveredFourthSupportDifference H B,
    p4Q2PZ32_originalD14_eq_coveredFourthSupportDifference H C]
  ring

/-- The complete remaining source of a deviation from the genuine
SU(2) Wilson low Ward baseline is an alternating fourth-support
determinant. This is an identity, NOT its nonzero proof. -/
theorem p4Q2PZ32_originalSixthWard_residual_exact
    (A B C : Cfg) :
    W6 A B C - Low6 A B C =
      -15*((w B-w A)*(S4 C-S4 A) -
           (w C-w A)*(S4 B-S4 A)) := by
  rw [p4Q2PZ32_originalSixthWard_onlyCoveredFourthSupport H A B C]
  ring

/-- CONDITIONAL representation-theoretic descent gate:
if the remaining genuine four-edge-covering Haar sum is affine in
the original spatial Wilson action, the full sixth Ward correction
vanishes. The premise is NOT established for the original SU(2) Haar. -/
theorem p4Q2PZ32_originalSixthWard_lowOnly_of_affineFourthSupport
    (κ c : ℝ)
    (hAffine : ∀ D : Cfg, S4 D = κ*w D+c)
    (A B C : Cfg) :
    W6 A B C = Low6 A B C := by
  rw [p4Q2PZ32_originalSixthWard_onlyCoveredFourthSupport H A B C,
    hAffine A, hAffine B, hAffine C]
  ring

/-- A genuine Ward correction beyond the original sixth-jet/low
profile is an obstruction to ANY affine description of the true
four-edge-covering Haar sum by the spatial Wilson action. -/
theorem p4Q2PZ32_originalSixthWard_residual_forces_nonaffineFourthSupport
    (A B C : Cfg)
    (hResidual : W6 A B C ≠ Low6 A B C) :
    ¬ ∃ κ c : ℝ, ∀ D : Cfg, S4 D = κ*w D+c := by
  rintro ⟨κ, c, hAffine⟩
  exact hResidual
    (p4Q2PZ32_originalSixthWard_lowOnly_of_affineFourthSupport
      H κ c hAffine A B C)

end OriginalAllPeriodsFourthSupportWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalF32_Haar_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalMixedPotential_onlyFourthDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalMixedPotential_sameSpatialAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalSixthWard_onlyFourthDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalD14_eq_coveredFourthSupportDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalSixthWard_onlyCoveredFourthSupport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalSixthWard_residual_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalSixthWard_lowOnly_of_affineFourthSupport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ32_originalSixthWard_residual_forces_nonaffineFourthSupport
