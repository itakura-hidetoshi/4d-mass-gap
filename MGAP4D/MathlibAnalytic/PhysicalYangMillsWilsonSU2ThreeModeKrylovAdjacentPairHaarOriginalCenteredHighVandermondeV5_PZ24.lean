import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLowWardProfileV5_PZ23
import Mathlib.Tactic

/-!
# P4-Q2-PZ24 — the two ORIGINAL centered higher Haar obstructions

PZ23 proved that the original physical fifth mixed potential
  V(B) = Profile(w(B)) + 70 F32(B) + 30 F23(I) + 5 F14(B)
has a genuine SU(2) Haar quartic low profile and has already
selected F23. This file uses the EXACT previous Haar identities to
show that all boundary variation of F32 comes from the original
centered spatial-cubic × two-crossing Haar moment, and all boundary
variation of F14 comes from the original centered spatial-linear ×
four-crossing Haar moment.

It then forms the true original sixth Ward obstruction. Crucially,
the first Taylor action coefficient a = -M1, so
  a(B)-a(A) = w(A)-w(B),
not the opposite. The low Haar quartic determinant is precisely
a three-spatial-configuration Vandermonde times an explicit real
symmetric quadratic polynomial of the authentic Haar coefficients.

The centerings, configurations, Haar measures, full Wilson one-slab
action, original spatial plaquettes and two physical posterior
sectors are unchanged. This is NOT a nonzero claim about either
remaining centered higher Haar obstruction, W6, rank3 or mass gap.
No independent posterior, fake spectrum, Dobrushin, new axiom,
sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ24_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ24_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ24_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ24_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ24_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ24_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section TrueWilsonCenteredHigherWard
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "F32" => p4Q2PZ22_originalSpatialCubeCrossingSquareHaar H
local notation "F14" => p4Q2PZ22_originalSpatialCrossingFourthHaar H
local notation "F23" => p4Q2PZ22_originalSpatialSquareCrossingCubeHaar H
local notation "Profile" => p4Q2PZ23_originalLowWardBoundaryProfile H
local notation "β2" => p4Q2PZ23_originalLowCoeffHaar2 H
local notation "β3" => p4Q2PZ23_originalLowCoeffHaar3 H
local notation "β4" => p4Q2PZ23_originalLowCoeffHaar4 H
local notation "V" => p4Q2PZ21_originalMixedFifthBoundaryPotential H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
  (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- This scalar is the true finite-volume Wilson spatial-half-action
mean on the ACTUAL Haar configuration, not a free parameter. -/
noncomputable def p4Q2PZ24_originalSpatialMean : ℝ :=
  ∫ X : Cfg, w X ∂haar

local notation "m" => p4Q2PZ24_originalSpatialMean H

private theorem p4Q2PZ24_half_continuous :
    Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ24_cross_continuous (D : Cfg) :
    Continuous (fun X : Cfg => Cross X D) := by
  have hp : Continuous (fun X : Cfg => (X,D)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

private theorem p4Q2PZ24_centered_continuous :
    Continuous (fun X : Cfg => h X) := by
  have hw := p4Q2PZ24_half_continuous H
  have hfun : (fun X : Cfg => h X) = (fun X : Cfg => m - w X) := by
    funext X
    exact p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H X
  rw [hfun]
  exact continuous_const.sub hw

/-- The only nonselected genuine spatial-cubic/two-crossing sector
after translating the original spatial Wilson half-action to its
PZ6-centered version h=m-w. -/
noncomputable def p4Q2PZ24_originalCenteredCubeCrossSquareHaar (D : Cfg) : ℝ :=
  ∫ X : Cfg, (h X)^3 * (Cross X D)^2 ∂haar

/-- The only nonselected genuine spatial-linear/four-crossing sector
after the original SU(2) fourth crossing Haar Ward is applied. -/
noncomputable def p4Q2PZ24_originalCenteredFirstCrossFourthHaar (D : Cfg) : ℝ :=
  ∫ X : Cfg, h X * (Cross X D)^4 ∂haar

local notation "Z32" => p4Q2PZ24_originalCenteredCubeCrossSquareHaar H
local notation "Z14" => p4Q2PZ24_originalCenteredFirstCrossFourthHaar H

/-- A boundary-normalized original SU(2) Haar obstruction, defined
directly from the genuine *centered spatial-cubic* two-crossing row. -/
noncomputable def p4Q2PZ24_originalCenteredCubeSquareDefect (D : Cfg) : ℝ :=
  Z32 D - Z32 I

/-- A boundary-normalized original SU(2) Haar obstruction, defined
directly from the genuine *centered spatial-linear* four-crossing row. -/
noncomputable def p4Q2PZ24_originalCenteredFirstFourthDefect (D : Cfg) : ℝ :=
  Z14 D - Z14 I

local notation "D32" => p4Q2PZ24_originalCenteredCubeSquareDefect H
local notation "D14" => p4Q2PZ24_originalCenteredFirstFourthDefect H

theorem p4Q2PZ24_originalCenteredDefects_atIdentity :
    D32 I = 0 ∧ D14 I = 0 := by
  constructor <;>
    simp [p4Q2PZ24_originalCenteredCubeSquareDefect,
      p4Q2PZ24_originalCenteredFirstFourthDefect]

/-- EXACT original SU(2) Haar expansion:
F14 = (mean w) * (four-crossing Haar) - (centered w × crossing-four Haar).
No independence or replacement of the temporal Wilson crossing. -/
theorem p4Q2PZ24_originalF14_centeredDecomposition (D : Cfg) :
    F14 D =
      m * (∫ X : Cfg, (Cross X D)^4 ∂haar) - Z14 D := by
  have hw := p4Q2PZ24_half_continuous H
  have hc := p4Q2PZ24_cross_continuous H D
  have hh := p4Q2PZ24_centered_continuous H
  have hiM : Integrable (fun X : Cfg => m*(Cross X D)^4) haar :=
    (continuous_const.mul (hc.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiH : Integrable (fun X : Cfg => h X*(Cross X D)^4) haar :=
    (hh.mul (hc.pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ X : Cfg, w X*(Cross X D)^4 ∂haar) =
    m*(∫ X : Cfg, (Cross X D)^4 ∂haar) -
      (∫ X : Cfg, h X*(Cross X D)^4 ∂haar)
  calc
    (∫ X : Cfg, w X*(Cross X D)^4 ∂haar) =
      (∫ X : Cfg, m*(Cross X D)^4 - h X*(Cross X D)^4 ∂haar) := by
        apply integral_congr_ae
        filter_upwards with X
        rw [p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H X]
        dsimp [p4Q2PZ24_originalSpatialMean]
        ring
    _ = m*(∫ X : Cfg, (Cross X D)^4 ∂haar) -
        (∫ X : Cfg, h X*(Cross X D)^4 ∂haar) := by
      simpa only [Pi.sub_apply, integral_const_mul] using
        (integral_sub hiM hiH)

/-- All true fourth-crossing boundary variation not carried by
the weighted spatial Wilson sector is a centered first Haar defect.
This uses PZ19's actual left Haar translation at degree four. -/
theorem p4Q2PZ24_originalF14_boundaryDifference_centered
    (B : Cfg) :
    F14 B - F14 I = -(Z14 B - Z14 I) := by
  have hB := p4Q2PZ24_originalF14_centeredDecomposition H B
  have hI := p4Q2PZ24_originalF14_centeredDecomposition H I
  rw [p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 4 B] at hB
  linarith

/-- F32 PLUS centered cubic has no unselected genuine Haar sectors:
the other terms are original unweighted, w-weighted and w²-weighted
CROSSING-SQUARE SU(2) Haar moments. -/
theorem p4Q2PZ24_originalF32_plusCenteredCube_lowerSelected
    (D : Cfg) :
    F32 D + Z32 D =
      m^3 * (∫ X : Cfg, (Cross X D)^2 ∂haar) -
      3*m^2 * (∫ X : Cfg, w X*(Cross X D)^2 ∂haar) +
      3*m * (∫ X : Cfg, (w X)^2*(Cross X D)^2 ∂haar) := by
  have hw := p4Q2PZ24_half_continuous H
  have hc := p4Q2PZ24_cross_continuous H D
  have hh := p4Q2PZ24_centered_continuous H
  have hiW3 : Integrable (fun X : Cfg => (w X)^3*(Cross X D)^2) haar :=
    ((hw.pow 3).mul (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiH3 : Integrable (fun X : Cfg => (h X)^3*(Cross X D)^2) haar :=
    ((hh.pow 3).mul (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi0 : Integrable (fun X : Cfg => m^3*(Cross X D)^2) haar :=
    (continuous_const.mul (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun X : Cfg =>
      (-3*m^2)*(w X*(Cross X D)^2)) haar :=
    (continuous_const.mul (hw.mul (hc.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun X : Cfg =>
      (3*m)*((w X)^2*(Cross X D)^2)) haar :=
    (continuous_const.mul ((hw.pow 2).mul (hc.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ X : Cfg, (w X)^3*(Cross X D)^2 ∂haar) +
      (∫ X : Cfg, (h X)^3*(Cross X D)^2 ∂haar) =
    m^3*(∫ X : Cfg, (Cross X D)^2 ∂haar) -
      3*m^2*(∫ X : Cfg, w X*(Cross X D)^2 ∂haar) +
      3*m*(∫ X : Cfg, (w X)^2*(Cross X D)^2 ∂haar)
  calc
    (∫ X : Cfg, (w X)^3*(Cross X D)^2 ∂haar) +
        (∫ X : Cfg, (h X)^3*(Cross X D)^2 ∂haar) =
      (∫ X : Cfg,
        (w X)^3*(Cross X D)^2 +
          (h X)^3*(Cross X D)^2 ∂haar) := by
          symm
          simpa only [Pi.add_apply] using (integral_add hiW3 hiH3)
    _ = (∫ X : Cfg,
        (m^3*(Cross X D)^2 +
          (-3*m^2)*(w X*(Cross X D)^2)) +
          (3*m)*((w X)^2*(Cross X D)^2) ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      rw [p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H X]
      dsimp [p4Q2PZ24_originalSpatialMean]
      ring
    _ = m^3*(∫ X : Cfg, (Cross X D)^2 ∂haar) -
        3*m^2*(∫ X : Cfg, w X*(Cross X D)^2 ∂haar) +
        3*m*(∫ X : Cfg, (w X)^2*(Cross X D)^2 ∂haar) := by
      have hadd01 :
          (∫ X : Cfg,
            m^3*(Cross X D)^2 +
              (-3*m^2)*(w X*(Cross X D)^2) ∂haar) =
          (∫ X : Cfg, m^3*(Cross X D)^2 ∂haar) +
            (∫ X : Cfg, (-3*m^2)*(w X*(Cross X D)^2) ∂haar) := by
        simpa only [Pi.add_apply] using (integral_add hi0 hi1)
      have hadd012 :
          (∫ X : Cfg,
            (m^3*(Cross X D)^2 +
              (-3*m^2)*(w X*(Cross X D)^2)) +
                (3*m)*((w X)^2*(Cross X D)^2) ∂haar) =
          (∫ X : Cfg,
            m^3*(Cross X D)^2 +
              (-3*m^2)*(w X*(Cross X D)^2) ∂haar) +
            (∫ X : Cfg, (3*m)*((w X)^2*(Cross X D)^2) ∂haar) := by
        simpa only [Pi.add_apply] using
          (integral_add (hi0.add hi1) hi2)
      rw [hadd012, hadd01]
      simp only [integral_const_mul]
      ring

/-- Exactly the genuine original SU(2) Haar boundary variation of
F32, with PZ19/PZ20's full crossing-square weighted Ward rules. -/
theorem p4Q2PZ24_originalF32_boundaryDifference_centered
    (B : Cfg) :
    F32 B - F32 I = -(Z32 B - Z32 I) := by
  have hB := p4Q2PZ24_originalF32_plusCenteredCube_lowerSelected H B
  have hI := p4Q2PZ24_originalF32_plusCenteredCube_lowerSelected H I
  rw [p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 2 B,
    p4Q2PZ19_originalHalfSpatial_crossingSquareHaar_invariant H B,
    p4Q2PZ20_originalHalfSpatialSquare_crossingSquareHaar_invariant H B] at hB
  linarith

theorem p4Q2PZ24_originalF32_eq_const_sub_defect (B : Cfg) :
    F32 B = F32 I - D32 B := by
  have hdiff := p4Q2PZ24_originalF32_boundaryDifference_centered H B
  unfold p4Q2PZ24_originalCenteredCubeSquareDefect
  linarith

theorem p4Q2PZ24_originalF14_eq_const_sub_defect (B : Cfg) :
    F14 B = F14 I - D14 B := by
  have hdiff := p4Q2PZ24_originalF14_boundaryDifference_centered H B
  unfold p4Q2PZ24_originalCenteredFirstFourthDefect
  linarith

/-- The full original physical mixed potential has precisely two
boundary-normalized centered SU(2) Haar defects. All other terms
are a true Haar quartic in the Wilson spatial action and genuine
SU(2) Haar constants. -/
theorem p4Q2PZ24_originalMixedPotential_centeredTwoDefects (B : Cfg) :
    V B =
      (Profile (w B)+70*F32 I+30*F23 I+5*F14 I) -
        70*D32 B-5*D14 B := by
  rw [p4Q2PZ23_originalMixedPotential_twoUnselectedHigh H B,
    p4Q2PZ24_originalF32_eq_const_sub_defect H B,
    p4Q2PZ24_originalF14_eq_const_sub_defect H B]
  ring

/-- A centered spatial-Wilson quartic carries a determinantal
Vandermonde shape: the real symmetric quadratic correction of three
TRUE boundary Wilson spatial actions. -/
noncomputable def p4Q2PZ24_originalLowWardSymmetricQuadratic
    (x y z : ℝ) : ℝ :=
  β2 + β3*(x+y+z) +
    β4*(x^2+y^2+z^2+x*y+x*z+y*z)

local notation "Shape" => p4Q2PZ24_originalLowWardSymmetricQuadratic H

/-- Exact, unconditioned three-configuration Vandermonde for the
genuine SU(2) Haar low profile from PZ23. It vanishes for repeated
spatial-action values, without assuming any nonzero Haar coefficient. -/
theorem p4Q2PZ24_originalLowWard_Vandermonde
    (x y z : ℝ) :
    (y-x)*(Profile z-Profile x)-(z-x)*(Profile y-Profile x) =
      (y-x)*(z-x)*(z-y)*Shape x y z := by
  rw [p4Q2PZ23_originalLowWardProfile_quartic H x,
    p4Q2PZ23_originalLowWardProfile_quartic H y,
    p4Q2PZ23_originalLowWardProfile_quartic H z]
  unfold p4Q2PZ24_originalLowWardSymmetricQuadratic
  ring

/-- Sign-critical original source identity: a is the negative
first Taylor action moment, so its DIFFERENCE is the reverse of the
monic original spatial Wilson action difference. -/
theorem p4Q2PZ24_originalFirstTaylorAction_spatialDifference
    (A B : Cfg) :
    a B-a A = w A-w B := by
  have hFirst :=
    p4Q2PZ17_originalFirstMoment_boundaryDifference H A B
  rw [p4Q2PZ17_originalFirstMoment_eq_negTaylorFirst H B,
    p4Q2PZ17_originalFirstMoment_eq_negTaylorFirst H A] at hFirst
  linarith

/-- The ORIGINAL sixth Wilson Ward obstruction with exact 720*C6,
positive low-sector Vandermonde sign (because a=-M1), and exactly
TWO original centered SU(2) Haar higher-sector boundary defects.
No boundary nonzero witness is asserted. -/
theorem p4Q2PZ24_originalSixthWard_centeredVandermonde
    (A B C : Cfg) :
    W6 A B C =
      720*C6 A B C +
      6*(w B-w A)*(w C-w A)*(w C-w B)*
        Shape (w A) (w B) (w C) -
      420*((w B-w A)*(D32 C-D32 A) -
        (w C-w A)*(D32 B-D32 A)) -
      30*((w B-w A)*(D14 C-D14 A) -
        (w C-w A)*(D14 B-D14 A)) := by
  have hVander := p4Q2PZ24_originalLowWard_Vandermonde H
    (w A) (w B) (w C)
  calc
    W6 A B C =
      720*C6 A B C +
      6*((w B-w A)*(Profile (w C)-Profile (w A)) -
        (w C-w A)*(Profile (w B)-Profile (w A))) -
      420*((w B-w A)*(D32 C-D32 A) -
        (w C-w A)*(D32 B-D32 A)) -
      30*((w B-w A)*(D14 C-D14 A) -
        (w C-w A)*(D14 B-D14 A)) := by
      rw [p4Q2PZ21_originalSixthWard_mixedPotential H A B C,
        p4Q2PZ24_originalFirstTaylorAction_spatialDifference H A B,
        p4Q2PZ24_originalFirstTaylorAction_spatialDifference H A C,
        p4Q2PZ24_originalMixedPotential_centeredTwoDefects H A,
        p4Q2PZ24_originalMixedPotential_centeredTwoDefects H B,
        p4Q2PZ24_originalMixedPotential_centeredTwoDefects H C]
      ring
    _ = 720*C6 A B C +
      6*(w B-w A)*(w C-w A)*(w C-w B)*
        Shape (w A) (w B) (w C) -
      420*((w B-w A)*(D32 C-D32 A) -
        (w C-w A)*(D32 B-D32 A)) -
      30*((w B-w A)*(D14 C-D14 A) -
        (w C-w A)*(D14 B-D14 A)) := by
      rw [hVander]
      ring

/-- Equal original spatial Wilson actions on ALL three configurations
annihilate the complete fifth mixed-potential Ward determinant.
Any sixth Ward contribution there must be in 720*C6 itself. -/
theorem p4Q2PZ24_originalSixthWard_equalSpatialActions
    (A B C : Cfg) (hAB : w A = w B) (hAC : w A = w C) :
    W6 A B C = 720*C6 A B C := by
  rw [p4Q2PZ24_originalSixthWard_centeredVandermonde H A B C,
    ←hAB, ←hAC]
  ring

/-- A precise honest sign gate for a later genuine finite-volume
three-configuration witness. The actual physical inequalities still
need independent proof from SU(2) Haar and the original Wilson kernel. -/
theorem p4Q2PZ24_originalSixthWard_positive_of_centeredVandermonde
    (A B C : Cfg)
    (hStrict :
      0 < 720*C6 A B C +
        6*(w B-w A)*(w C-w A)*(w C-w B)*
          Shape (w A) (w B) (w C) -
        420*((w B-w A)*(D32 C-D32 A) -
          (w C-w A)*(D32 B-D32 A)) -
        30*((w B-w A)*(D14 C-D14 A) -
          (w C-w A)*(D14 B-D14 A))) :
    0 < W6 A B C := by
  rw [p4Q2PZ24_originalSixthWard_centeredVandermonde H A B C]
  exact hStrict

end TrueWilsonCenteredHigherWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalCenteredDefects_atIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalF14_centeredDecomposition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalF14_boundaryDifference_centered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalF32_plusCenteredCube_lowerSelected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalF32_boundaryDifference_centered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalF32_eq_const_sub_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalF14_eq_const_sub_defect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalMixedPotential_centeredTwoDefects
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalLowWard_Vandermonde
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalFirstTaylorAction_spatialDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalSixthWard_centeredVandermonde
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalSixthWard_equalSpatialActions
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ24_originalSixthWard_positive_of_centeredVandermonde
