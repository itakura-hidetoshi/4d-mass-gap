import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalUnconditionalSeventhOrderV5_PZ37A
import Mathlib.Tactic

/-!
# P4-Q2-PZ37B — original physical sixth Haar moments in the seventh coefficient

PZ37A proves the original interacting Wilson minor is O(beta^7).
The seventh coefficient of a fifth-order Taylor *jet* in PZ1 is not
yet the seventh coefficient of the physical original Wilson minor:
the actual sixth one-slab and two-slab moments enter through the (1,6) and
(6,1) determinant pair. This file retains that correction exactly.

Every coefficient below is from the ORIGINAL S(X,B) and the complete
Q(Y,X,B)=S(Y,X)+S(X,B), with the original normalized spatial Haar.
In particular, the middle spatial Wilson action is not removed.
This is an EXACT degree-six integrated-moment polynomial identity,
not yet an eighth-order analytic estimate for the literal kernel,
a seventh coefficient numerical evaluation, a sign/nonzero witness,
a volume-uniform bound, or a continuum mass-gap theorem.

No new axioms, sorry, admit, native_decide proof replacement or
independent spectral/posterior model.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section OriginalSeventhPhysicalCoefficient

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H
local notation "m" => p4Q2PZ1_originalOneSlabFifthActionMoment H
local notation "n" => p4Q2PZ1_originalTwoSlabFifthActionMoment H
local notation "r₁" => p4Q2PZ36D_originalOneRaw H 6
local notation "r₂" => p4Q2PZ36D_originalTwoRaw H 6
local notation "J₁" => p4Q2PZ1_originalOneSlabFormalTaylor5 H
local notation "J₂" => p4Q2PZ1_originalTwoSlabFormalTaylor5 H
local notation "D6" => p4Q2PZ1_originalSixthFifthJetCoefficient H
local notation "D7" => p4Q2PZ1_originalSeventhFifthJetCoefficient H
local notation "D8" => p4Q2PZ1_originalEighthFifthJetCoefficient H
local notation "D9" => p4Q2PZ1_originalNinthFifthJetCoefficient H
local notation "D10" => p4Q2PZ1_originalTenthFifthJetCoefficient H

/-- A signed, oriented boundary determinant for *actual* source functions. -/
noncomputable def p4Q2PZ37B_originalBoundaryWedge
    (f h : Cfg → ℝ) (A B C : Cfg) : ℝ :=
  (f B - f A) * (h C - h A) -
    (f C - f A) * (h B - h A)

local notation "W" => p4Q2PZ37B_originalBoundaryWedge H

/-- One-slab sixth Wilson moment and two-slab sixth Wilson moment are
the pre-existing PZ36D genuine Haar integrals, not free parameters. -/
noncomputable def p4Q2PZ37B_originalOneSlabTaylor6
    (beta : ℝ) (B : Cfg) : ℝ :=
  J₁ beta B + beta ^ 6 / 720 * r₁ B

noncomputable def p4Q2PZ37B_originalTwoSlabTaylor6
    (beta : ℝ) (B : Cfg) : ℝ :=
  J₂ beta B + beta ^ 6 / 720 * r₂ B

local notation "T₁" => p4Q2PZ37B_originalOneSlabTaylor6 H
local notation "T₂" => p4Q2PZ37B_originalTwoSlabTaylor6 H

/-- Exact seventh coefficient of the ORIGINAL SIXTH-moment Taylor jet.
PZ1's old D7 is missing the explicitly displayed sixth-action-moment
correction. The common first Taylor row is the genuine a from PK. -/
noncomputable def p4Q2PZ37B_originalPhysicalSeventhCoefficient
    (A B C : Cfg) : ℝ :=
  D7 A B C +
    W a (fun D => r₂ D - r₁ D) A B C / 720

/-- Higher coefficients are retained to make the seventh coefficient an
exact polynomial identity (rather than an unverified coefficient guess). -/
noncomputable def p4Q2PZ37B_originalPhysicalEighthCoefficient
    (A B C : Cfg) : ℝ :=
  D8 A B C +
    (W b r₂ A B C +
      W r₁ (fun D => b D + 2 * d D) A B C) / 1440

noncomputable def p4Q2PZ37B_originalPhysicalNinthCoefficient
    (A B C : Cfg) : ℝ :=
  D9 A B C + (W c r₂ A B C + W r₁ g A B C) / 4320

noncomputable def p4Q2PZ37B_originalPhysicalTenthCoefficient
    (A B C : Cfg) : ℝ :=
  D10 A B C + (W u r₂ A B C + W r₁ v A B C) / 17280

noncomputable def p4Q2PZ37B_originalPhysicalEleventhCoefficient
    (A B C : Cfg) : ℝ :=
  -(W m r₂ A B C + W r₁ n A B C) / 86400

noncomputable def p4Q2PZ37B_originalPhysicalTwelfthCoefficient
    (A B C : Cfg) : ℝ :=
  W r₁ r₂ A B C / 518400

local notation "P7" => p4Q2PZ37B_originalPhysicalSeventhCoefficient H
local notation "P8" => p4Q2PZ37B_originalPhysicalEighthCoefficient H
local notation "P9" => p4Q2PZ37B_originalPhysicalNinthCoefficient H
local notation "P10" => p4Q2PZ37B_originalPhysicalTenthCoefficient H
local notation "P11" => p4Q2PZ37B_originalPhysicalEleventhCoefficient H
local notation "P12" => p4Q2PZ37B_originalPhysicalTwelfthCoefficient H

private theorem p4Q2PZ37B_originalOneFifthJet_difference
    (beta : ℝ) (A D : Cfg) :
    J₁ beta D - J₁ beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * (b D - b A) +
        beta ^ 3 / 6 * (c D - c A) +
        beta ^ 4 / 24 * (u D - u A) -
        beta ^ 5 / 120 * (m D - m A) := by
  unfold p4Q2PZ1_originalOneSlabFormalTaylor5
    p4Q2PX_originalOneSlabFormalTaylor4
    p4Q2PP2_originalOneSlabFormalTaylor3
    p4Q2PK_originalOneSlabFormalTaylor2
  ring

private theorem p4Q2PZ37B_originalTwoFifthJet_difference
    (beta : ℝ) (A D : Cfg) :
    J₂ beta D - J₂ beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) +
        beta ^ 3 / 6 * (g D - g A) +
        beta ^ 4 / 24 * (v D - v A) -
        beta ^ 5 / 120 * (n D - n A) := by
  unfold p4Q2PZ1_originalTwoSlabFormalTaylor5
    p4Q2PX_originalTwoSlabFormalTaylor4
    p4Q2PP2_originalTwoSlabFormalTaylor3
    p4Q2PK_originalTwoSlabFormalTaylor2
  dsimp only
  ring

/-- Exact original physical six-moment Taylor-jet determinant through
degree twelve, with ALL real coefficient signs fixed by e^(-beta*S).
The physical sixth Ward D6 remains explicit in this identity. -/
theorem p4Q2PZ37B_originalSixthMomentJetMinor_exact
    (beta : ℝ) (A B C : Cfg) :
    (T₁ beta B - T₁ beta A) * (T₂ beta C - T₂ beta A) -
      (T₁ beta C - T₁ beta A) * (T₂ beta B - T₂ beta A) =
      beta ^ 6 * D6 A B C +
        beta ^ 7 * P7 A B C +
        beta ^ 8 * P8 A B C +
        beta ^ 9 * P9 A B C +
        beta ^ 10 * P10 A B C +
        beta ^ 11 * P11 A B C +
        beta ^ 12 * P12 A B C := by
  calc
    (T₁ beta B - T₁ beta A) * (T₂ beta C - T₂ beta A) -
      (T₁ beta C - T₁ beta A) * (T₂ beta B - T₂ beta A) =
      ((J₁ beta B - J₁ beta A) * (J₂ beta C - J₂ beta A) -
        (J₁ beta C - J₁ beta A) * (J₂ beta B - J₂ beta A)) +
      beta ^ 6 / 720 *
        ((J₁ beta B - J₁ beta A) * (r₂ C - r₂ A) -
          (J₁ beta C - J₁ beta A) * (r₂ B - r₂ A) +
          (r₁ B - r₁ A) * (J₂ beta C - J₂ beta A) -
          (r₁ C - r₁ A) * (J₂ beta B - J₂ beta A)) +
      beta ^ 12 / 518400 * W r₁ r₂ A B C := by
        unfold p4Q2PZ37B_originalOneSlabTaylor6
          p4Q2PZ37B_originalTwoSlabTaylor6
          p4Q2PZ37B_originalBoundaryWedge
        ring
    _ = beta ^ 6 * D6 A B C +
        beta ^ 7 * P7 A B C +
        beta ^ 8 * P8 A B C +
        beta ^ 9 * P9 A B C +
        beta ^ 10 * P10 A B C +
        beta ^ 11 * P11 A B C +
        beta ^ 12 * P12 A B C := by
      rw [p4Q2PZ1_originalFifthMomentJetMinor_afterUniversalWard H beta A B C,
        p4Q2PZ37B_originalOneFifthJet_difference H beta A B,
        p4Q2PZ37B_originalOneFifthJet_difference H beta A C,
        p4Q2PZ37B_originalTwoFifthJet_difference H beta A C,
        p4Q2PZ37B_originalTwoFifthJet_difference H beta A B]
      unfold p4Q2PZ37B_originalPhysicalSeventhCoefficient
        p4Q2PZ37B_originalPhysicalEighthCoefficient
        p4Q2PZ37B_originalPhysicalNinthCoefficient
        p4Q2PZ37B_originalPhysicalTenthCoefficient
        p4Q2PZ37B_originalPhysicalEleventhCoefficient
        p4Q2PZ37B_originalPhysicalTwelfthCoefficient
        p4Q2PZ37B_originalBoundaryWedge
      ring

/-- The PZ36I genuine sixth Ward cancellation eliminates D6 without
eliminating or assigning any unproved seventh coefficient. -/
theorem p4Q2PZ37B_originalSixthMomentJet_afterUnconditionalWard
    (beta : ℝ) (A B C : Cfg) :
    (T₁ beta B - T₁ beta A) * (T₂ beta C - T₂ beta A) -
      (T₁ beta C - T₁ beta A) * (T₂ beta B - T₂ beta A) =
        beta ^ 7 * P7 A B C +
        beta ^ 8 * P8 A B C +
        beta ^ 9 * P9 A B C +
        beta ^ 10 * P10 A B C +
        beta ^ 11 * P11 A B C +
        beta ^ 12 * P12 A B C := by
  rw [p4Q2PZ37B_originalSixthMomentJetMinor_exact H beta A B C,
    p4Q2PZ36I_originalCorrectedSixthJet_unconditional_zero H A B C]
  ring

end OriginalSeventhPhysicalCoefficient
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37B_originalSixthMomentJetMinor_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37B_originalSixthMomentJet_afterUnconditionalWard
