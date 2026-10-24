import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalUniversalFifthWardZeroV5_PY9D
import Mathlib.Tactic

/-!
# P4-Q2-PZ1 — true fifth Wilson action moments and the corrected sixth jet

The ORIGINAL SU(2) one-slab Wilson action S(X,B), and the complete
two-slab action Q(X,A,B)=S(X,A)+S(A,B) with its unchanged intermediate
spatial plaquette action, define actual fifth action moments:
  m₅(B)=∫ S(X,B)^5 dHaar(X)
  n₅(B)=∫∫ Q(X,A,B)^5 dHaar(X) dHaar(A).
The exponential e^(-beta*S) has NEGATIVE fifth Taylor coefficient;
therefore the genuine fifth-action-moment formal rows are
  J5_one=J4_one-beta^5*m₅/120,
  J5_two=J4_two-beta^5*n₅/120.

The exact determinant's degree-six coefficient is NOT simply the
previous fourth-jet C6: it includes the extra fifth-moment correction
  -(1/120) det(Δa, Δ(n₅-m₅)).
The full fifth-jet minor is an exact polynomial of degrees 5 through
10; the already established genuine Ward C5=0 makes degree 6 leading.
This is an EXACT identity for integrated original action MOMENTS.
Establishing an analytic O(beta^7) remainder for the literal Wilson
minor is a SEPARATE step; this file does not claim that bridge.

No changed Wilson action, decoupled posterior, spectral surrogate,
Dobrushin shortcut, added axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section OriginalFifthMomentSixthJet

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H
local notation "J4₁" => p4Q2PX_originalOneSlabFormalTaylor4 H
local notation "J4₂" => p4Q2PX_originalTwoSlabFormalTaylor4 H
local notation "C5" => p4Q2PX_originalFifthFourthJetCoefficient H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "C7" => p4Q2PX_originalSeventhFourthJetCoefficient H
local notation "C8" => p4Q2PX_originalEighthFourthJetCoefficient H

/-- Actual fifth action moment of the ORIGINAL spatial one-slab Wilson action. -/
noncomputable def p4Q2PZ1_originalOneSlabFifthActionMoment (B : Cfg) : ℝ :=
  ∫ X : Cfg, (S X B) ^ 5 ∂haar

/-- Actual fifth action moment of the complete, INTERACTING two-slab action.
This double Haar integral retains ALL middle-slice spatial Wilson terms. -/
noncomputable def p4Q2PZ1_originalTwoSlabFifthActionMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 5 ∂haar ∂haar

local notation "m" => p4Q2PZ1_originalOneSlabFifthActionMoment H
local notation "n" => p4Q2PZ1_originalTwoSlabFifthActionMoment H

/-- Correct sign of the original one-slab exponential fifth-order moment. -/
noncomputable def p4Q2PZ1_originalOneSlabFormalTaylor5
    (beta : ℝ) (B : Cfg) : ℝ :=
  J4₁ beta B - beta ^ 5 / 120 * m B

/-- Correct sign of the original two-slab exponential fifth-order moment. -/
noncomputable def p4Q2PZ1_originalTwoSlabFormalTaylor5
    (beta : ℝ) (B : Cfg) : ℝ :=
  J4₂ beta B - beta ^ 5 / 120 * n B

local notation "J5₁" => p4Q2PZ1_originalOneSlabFormalTaylor5 H
local notation "J5₂" => p4Q2PZ1_originalTwoSlabFormalTaylor5 H

/-- The corrected SIXTH coefficient of the true fifth-action-moment
Wilson jet contains the previously missing Δa∧Δ(n-m) determinant. -/
noncomputable def p4Q2PZ1_originalSixthFifthJetCoefficient
    (A B C : Cfg) : ℝ :=
  C6 A B C -
    ((a B - a A) * ((n C - n A) - (m C - m A)) -
     (a C - a A) * ((n B - n A) - (m B - m A))) / 120

/-- Exact degree-seven coefficient of the original fifth-moment jet. -/
noncomputable def p4Q2PZ1_originalSeventhFifthJetCoefficient
    (A B C : Cfg) : ℝ :=
  C7 A B C -
    ((b B - b A) * (n C - n A) -
     (b C - b A) * (n B - n A) +
     (m B - m A) * ((b C - b A) + 2 * (d C - d A)) -
     (m C - m A) * ((b B - b A) + 2 * (d B - d A))) / 240

/-- Exact degree-eight coefficient of the original fifth-moment jet. -/
noncomputable def p4Q2PZ1_originalEighthFifthJetCoefficient
    (A B C : Cfg) : ℝ :=
  C8 A B C -
    ((c B - c A) * (n C - n A) -
     (c C - c A) * (n B - n A) +
     (m B - m A) * (g C - g A) -
     (m C - m A) * (g B - g A)) / 720

/-- Exact degree-nine coefficient of the original fifth-moment jet. -/
noncomputable def p4Q2PZ1_originalNinthFifthJetCoefficient
    (A B C : Cfg) : ℝ :=
  - ((u B - u A) * (n C - n A) -
     (u C - u A) * (n B - n A) +
     (m B - m A) * (v C - v A) -
     (m C - m A) * (v B - v A)) / 2880

/-- Exact degree-ten coefficient of the original fifth-moment jet. -/
noncomputable def p4Q2PZ1_originalTenthFifthJetCoefficient
    (A B C : Cfg) : ℝ :=
  ((m B - m A) * (n C - n A) -
   (m C - m A) * (n B - n A)) / 14400

local notation "D6" => p4Q2PZ1_originalSixthFifthJetCoefficient H
local notation "D7" => p4Q2PZ1_originalSeventhFifthJetCoefficient H
local notation "D8" => p4Q2PZ1_originalEighthFifthJetCoefficient H
local notation "D9" => p4Q2PZ1_originalNinthFifthJetCoefficient H
local notation "D10" => p4Q2PZ1_originalTenthFifthJetCoefficient H

/-- The original fourth-order one-slab moment row, explicitly expanded
without changing the integrated Wilson action. -/
private theorem p4Q2PZ1_oneSlabFourthRow_difference
    (beta : ℝ) (A D : Cfg) :
    J4₁ beta D - J4₁ beta A =
      beta * (a D - a A) +
      beta ^ 2 / 2 * (b D - b A) +
      beta ^ 3 / 6 * (c D - c A) +
      beta ^ 4 / 24 * (u D - u A) := by
  unfold p4Q2PX_originalOneSlabFormalTaylor4
    p4Q2PP2_originalOneSlabFormalTaylor3
    p4Q2PK_originalOneSlabFormalTaylor2
  ring

/-- The original fourth-order two-slab moment row, retaining the
genuine mixed two-slab moment d. -/
private theorem p4Q2PZ1_twoSlabFourthRow_difference
    (beta : ℝ) (A D : Cfg) :
    J4₂ beta D - J4₂ beta A =
      beta * (a D - a A) +
      beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) +
      beta ^ 3 / 6 * (g D - g A) +
      beta ^ 4 / 24 * (v D - v A) := by
  unfold p4Q2PX_originalTwoSlabFormalTaylor4
    p4Q2PP2_originalTwoSlabFormalTaylor3
    p4Q2PK_originalTwoSlabFormalTaylor2
  dsimp only
  ring

/-- Exact polynomial identity for the ORIGINAL fifth-moment Wilson jet.
The former fourth-moment fifth coefficient C5 and all five new
degree-six-through-ten coefficients are retained with their real signs. -/
theorem p4Q2PZ1_originalFifthMomentJetMinor_exact
    (beta : ℝ) (A B C : Cfg) :
    (J5₁ beta B - J5₁ beta A) * (J5₂ beta C - J5₂ beta A) -
      (J5₁ beta C - J5₁ beta A) * (J5₂ beta B - J5₂ beta A) =
      beta ^ 5 * C5 A B C +
      beta ^ 6 * D6 A B C + beta ^ 7 * D7 A B C +
      beta ^ 8 * D8 A B C + beta ^ 9 * D9 A B C +
      beta ^ 10 * D10 A B C := by
  have hExpand :
      (J5₁ beta B - J5₁ beta A) * (J5₂ beta C - J5₂ beta A) -
        (J5₁ beta C - J5₁ beta A) * (J5₂ beta B - J5₂ beta A) =
      ((J4₁ beta B - J4₁ beta A) * (J4₂ beta C - J4₂ beta A) -
        (J4₁ beta C - J4₁ beta A) * (J4₂ beta B - J4₂ beta A)) -
      beta ^ 5 / 120 *
        ((J4₁ beta B - J4₁ beta A) * (n C - n A) -
          (J4₁ beta C - J4₁ beta A) * (n B - n A) +
          (m B - m A) * (J4₂ beta C - J4₂ beta A) -
          (m C - m A) * (J4₂ beta B - J4₂ beta A)) +
      beta ^ 10 / 14400 *
        ((m B - m A) * (n C - n A) -
          (m C - m A) * (n B - n A)) := by
    unfold p4Q2PZ1_originalOneSlabFormalTaylor5
      p4Q2PZ1_originalTwoSlabFormalTaylor5
    ring
  calc
    (J5₁ beta B - J5₁ beta A) * (J5₂ beta C - J5₂ beta A) -
      (J5₁ beta C - J5₁ beta A) * (J5₂ beta B - J5₂ beta A) =
      ((J4₁ beta B - J4₁ beta A) * (J4₂ beta C - J4₂ beta A) -
        (J4₁ beta C - J4₁ beta A) * (J4₂ beta B - J4₂ beta A)) -
      beta ^ 5 / 120 *
        ((J4₁ beta B - J4₁ beta A) * (n C - n A) -
          (J4₁ beta C - J4₁ beta A) * (n B - n A) +
          (m B - m A) * (J4₂ beta C - J4₂ beta A) -
          (m C - m A) * (J4₂ beta B - J4₂ beta A)) +
      beta ^ 10 / 14400 *
        ((m B - m A) * (n C - n A) -
          (m C - m A) * (n B - n A)) := hExpand
    _ = beta ^ 5 * C5 A B C +
      beta ^ 6 * D6 A B C + beta ^ 7 * D7 A B C +
      beta ^ 8 * D8 A B C + beta ^ 9 * D9 A B C +
      beta ^ 10 * D10 A B C := by
        rw [p4Q2PX_originalFourthMomentJetMinor_afterActualWard H beta A B C,
          p4Q2PZ1_oneSlabFourthRow_difference H beta A B,
          p4Q2PZ1_oneSlabFourthRow_difference H beta A C,
          p4Q2PZ1_twoSlabFourthRow_difference H beta A B,
          p4Q2PZ1_twoSlabFourthRow_difference H beta A C]
        unfold p4Q2PZ1_originalSixthFifthJetCoefficient
          p4Q2PZ1_originalSeventhFifthJetCoefficient
          p4Q2PZ1_originalEighthFifthJetCoefficient
          p4Q2PZ1_originalNinthFifthJetCoefficient
          p4Q2PZ1_originalTenthFifthJetCoefficient
        ring

/-- All original even periods obey the true Ward fifth-coefficient
cancellation; hence the genuine integrated fifth-moment JET begins
at sixth order, with the full corrected D6 coefficient. -/
theorem p4Q2PZ1_originalFifthMomentJetMinor_afterUniversalWard
    (beta : ℝ) (A B C : Cfg) :
    (J5₁ beta B - J5₁ beta A) * (J5₂ beta C - J5₂ beta A) -
      (J5₁ beta C - J5₁ beta A) * (J5₂ beta B - J5₂ beta A) =
      beta ^ 6 * D6 A B C + beta ^ 7 * D7 A B C +
      beta ^ 8 * D8 A B C + beta ^ 9 * D9 A B C +
      beta ^ 10 * D10 A B C := by
  rw [p4Q2PZ1_originalFifthMomentJetMinor_exact H beta A B C,
    p4Q2PY9_originalFifthFourthJetCoefficient_zero_allPeriods H A B C]
  ring

end OriginalFifthMomentSixthJet
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ1_originalFifthMomentJetMinor_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ1_originalFifthMomentJetMinor_afterUniversalWard
