import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalQuarticWardVanishesV5_PW3
import Mathlib.Tactic

/-!
# P4-Q2-PX — genuine quartic Wilson Haar moments and the FULL fifth-order formal jet

The original full SU(2) Wilson one-slab S(X,B) and interacting
two-slab Q(X,A,B)=S(X,A)+S(A,B) (with the complete middle
spatial plaquette contribution) define authentic FOURTH action moments
  u(B) = ∫ S(X,B)^4 dHaar(X)
  v(B) = ∫∫ Q(X,A,B)^4 dHaar(X) dHaar(A).

These extend PP2's degree-three Haar-moment jets to degree FOUR.
Unlike PP2's *cubic-jet* fifth coefficient, the actual fourth-
moment jet has an additional linear×quartic cross contribution:
  C5_fourthJet = C5_cubicJet
    + det(Δa, Δ(v-u))/24.

Using PW3's proved (not assumed) quartic Ward cancellation, the
entire degree-four-jet three-configuration minor is EXACTLY
  beta^5*C5_fourthJet + beta^6*C6 + beta^7*C7 + beta^8*C8.

This is an algebraic identity for jets built from the unchanged
actual Wilson Haar moments. It does NOT yet identify C5_fourthJet
with the literal analytic coefficient: the genuine fifth-order
one/two-slab integrated Taylor remainders and determinant O(beta^6)
stability must still be proved. C5 is not assumed nonzero.
No new axiom, sorry/admit, posterior substitution, Dobrushin or
surrogate spectral measure; no mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalFourthMomentsAndFifthJet
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
local notation "J1" => p4Q2PP2_originalOneSlabFormalTaylor3 H
local notation "J2" => p4Q2PP2_originalTwoSlabFormalTaylor3 H

/-- Exact original fourth power action moment under unchanged spatial Haar. -/
noncomputable def p4Q2PX_originalOneSlabFourthActionMoment
    (B : Cfg) : ℝ :=
  ∫ X : Cfg, (S X B) ^ 4 ∂haar

/-- Exact full two-slab fourth power action moment under both Haar
integrations, retaining the entire intermediate spatial Wilson action. -/
noncomputable def p4Q2PX_originalTwoSlabFourthActionMoment
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, ∫ X : Cfg, (Q X A B) ^ 4 ∂haar ∂haar

local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H

/-- Both true fourth action moments are nonnegative. -/
theorem p4Q2PX_originalOneSlabFourthActionMoment_nonneg (B : Cfg) :
    0 ≤ u B := by
  unfold p4Q2PX_originalOneSlabFourthActionMoment
  apply integral_nonneg
  intro X
  positivity

theorem p4Q2PX_originalTwoSlabFourthActionMoment_nonneg (B : Cfg) :
    0 ≤ v B := by
  unfold p4Q2PX_originalTwoSlabFourthActionMoment
  apply integral_nonneg
  intro A
  apply integral_nonneg
  intro X
  positivity

/-- Degree-four jets in the actual original Wilson action moments.
The analytic Taylor remainder is deliberately NOT claimed here. -/
noncomputable def p4Q2PX_originalOneSlabFormalTaylor4
    (beta : ℝ) (B : Cfg) : ℝ :=
  J1 beta B + beta ^ 4 / 24 * u B

noncomputable def p4Q2PX_originalTwoSlabFormalTaylor4
    (beta : ℝ) (B : Cfg) : ℝ :=
  J2 beta B + beta ^ 4 / 24 * v B

local notation "J4₁" => p4Q2PX_originalOneSlabFormalTaylor4 H
local notation "J4₂" => p4Q2PX_originalTwoSlabFormalTaylor4 H

/-- New fifth-order cross correction: linear jet times genuine
fourth moment, absent from the earlier cubic-only PP2 fifth jet. -/
noncomputable def p4Q2PX_originalFifthFourthJetCoefficient
    (A B C : Cfg) : ℝ :=
  p4Q2PP2_originalFifthJetCoefficient H A B C +
  ((a B - a A) * ((v C - v A) - (u C - u A)) -
   (a C - a A) * ((v B - v A) - (u B - u A))) / 24

noncomputable def p4Q2PX_originalSixthFourthJetCoefficient
    (A B C : Cfg) : ℝ :=
  p4Q2PP2_originalSixthJetCoefficient H A B C +
  ((b B - b A) * (v C - v A) -
    (b C - b A) * (v B - v A) +
    (u B - u A) * ((b C - b A) + 2 * (d C - d A)) -
    (u C - u A) * ((b B - b A) + 2 * (d B - d A))) / 48

noncomputable def p4Q2PX_originalSeventhFourthJetCoefficient
    (A B C : Cfg) : ℝ :=
  ((c B - c A) * (v C - v A) -
    (c C - c A) * (v B - v A) +
    (u B - u A) * (g C - g A) -
    (u C - u A) * (g B - g A)) / 144

noncomputable def p4Q2PX_originalEighthFourthJetCoefficient
    (A B C : Cfg) : ℝ :=
  ((u B - u A) * (v C - v A) -
    (u C - u A) * (v B - v A)) / 576

local notation "C5" => p4Q2PX_originalFifthFourthJetCoefficient H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "C7" => p4Q2PX_originalSeventhFourthJetCoefficient H
local notation "C8" => p4Q2PX_originalEighthFourthJetCoefficient H

private theorem p4Q2PX_oneSlabCubicJet_difference
    (beta : ℝ) (A D : Cfg) :
    J1 beta D - J1 beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * (b D - b A) +
          beta ^ 3 / 6 * (c D - c A) := by
  unfold p4Q2PP2_originalOneSlabFormalTaylor3
    p4Q2PK_originalOneSlabFormalTaylor2
  ring

private theorem p4Q2PX_twoSlabCubicJet_difference
    (beta : ℝ) (A D : Cfg) :
    J2 beta D - J2 beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) +
          beta ^ 3 / 6 * (g D - g A) := by
  unfold p4Q2PP2_originalTwoSlabFormalTaylor3
    p4Q2PK_originalTwoSlabFormalTaylor2
  dsimp only
  ring

/-- After genuine cubic AND quartic Ward cancellations, the complete
FOURTH-action-moment Wilson minor jet starts at the correctly
renormalized fifth coefficient. Algebraic identity, not an analytic
fifth coefficient claim or an assertion of nonvanishing. -/
theorem p4Q2PX_originalFourthMomentJetMinor_afterActualWard
    (beta : ℝ) (A B C : Cfg) :
    (J4₁ beta B - J4₁ beta A) * (J4₂ beta C - J4₂ beta A) -
      (J4₁ beta C - J4₁ beta A) * (J4₂ beta B - J4₂ beta A) =
      beta ^ 5 * C5 A B C + beta ^ 6 * C6 A B C +
      beta ^ 7 * C7 A B C + beta ^ 8 * C8 A B C := by
  have hCubic :=
    p4Q2PP2_originalCubicJetMinor_afterWard H beta A B C
  rw [p4Q2PW3_originalFourthCoefficient_zero H A B C] at hCubic
  have hOneB := p4Q2PX_oneSlabCubicJet_difference H beta A B
  have hOneC := p4Q2PX_oneSlabCubicJet_difference H beta A C
  have hTwoB := p4Q2PX_twoSlabCubicJet_difference H beta A B
  have hTwoC := p4Q2PX_twoSlabCubicJet_difference H beta A C
  have hExpand :
      (J4₁ beta B - J4₁ beta A) * (J4₂ beta C - J4₂ beta A) -
        (J4₁ beta C - J4₁ beta A) * (J4₂ beta B - J4₂ beta A) =
      ((J1 beta B - J1 beta A) * (J2 beta C - J2 beta A) -
        (J1 beta C - J1 beta A) * (J2 beta B - J2 beta A)) +
      beta ^ 4 / 24 *
        ((J1 beta B - J1 beta A) * (v C - v A) -
          (J1 beta C - J1 beta A) * (v B - v A) +
          (u B - u A) * (J2 beta C - J2 beta A) -
          (u C - u A) * (J2 beta B - J2 beta A)) +
      beta ^ 8 / 576 *
        ((u B - u A) * (v C - v A) -
          (u C - u A) * (v B - v A)) := by
    unfold p4Q2PX_originalOneSlabFormalTaylor4
      p4Q2PX_originalTwoSlabFormalTaylor4
    ring
  rw [hExpand, hCubic, hOneB, hOneC, hTwoB, hTwoC]
  unfold p4Q2PX_originalFifthFourthJetCoefficient
    p4Q2PX_originalSixthFourthJetCoefficient
    p4Q2PX_originalSeventhFourthJetCoefficient
    p4Q2PX_originalEighthFourthJetCoefficient
  ring

/-- Distinguish the original fourth-moment fifth coefficient
from the older cubic-jet fifth coefficient without approximations. -/
theorem p4Q2PX_originalFifthJet_correction_exact (A B C : Cfg) :
    C5 A B C - p4Q2PP2_originalFifthJetCoefficient H A B C =
      ((a B - a A) * ((v C - v A) - (u C - u A)) -
        (a C - a A) * ((v B - v A) - (u B - u A))) / 24 := by
  unfold p4Q2PX_originalFifthFourthJetCoefficient
  ring

end OriginalFourthMomentsAndFifthJet
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX_originalOneSlabFourthActionMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX_originalTwoSlabFourthActionMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX_originalFourthMomentJetMinor_afterActualWard
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX_originalFifthJet_correction_exact
