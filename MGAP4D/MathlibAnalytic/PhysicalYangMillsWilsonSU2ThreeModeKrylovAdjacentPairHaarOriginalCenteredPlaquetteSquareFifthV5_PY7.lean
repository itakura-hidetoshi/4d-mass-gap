import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthSpatialSquareObstructionV5_PY6E
import Mathlib.Tactic

/-!
# P4-Q2-PY7 — the TRUE fifth Wilson coefficient is a centered plaquette-square Haar minor

PY6 establishes that the genuine analytic fifth coefficient is 3/4
times the minor of the original first Wilson moment and
  F(B)=∫ (W(A)/2)^2 Cross(A,B)^2 dHaar(A).

The genuinely centered first moment h(A)=mean(w)-w(A) is EXACTLY
one half the sum of ALL original spatial SU(2) plaquette characters,
and is orthogonal to Cross(A,B)^2 by the proved PW3 center Ward.

Therefore F(B)=mean(w)^2 * mean(Cross^2) + G(B), with
  G(B)=∫ h(A)^2 Cross(A,B)^2 dHaar(A).
The first term is right-boundary constant by PY6; hence the true
fifth coefficient sees ONLY G, equivalently one quarter of
  ∫ (sum_p chi_p(A))^2 Cross(A,B)^2 dHaar(A).

This does NOT claim that diagonal/off-diagonal plaquette products
are nonzero, zero, or independent of the original right boundary.
All spatial Haar integrals and original full Wilson temporal crossing
and middle-slice spatial plaquette action remain untouched.
No substitute posterior, spectral measure, Dobrushin, new axiom,
sorry/admit or continuum Yang-Mills mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY7_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY7_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY7_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY7_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY7_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalCenteredSquareFifth
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "F" => p4Q2PY6_originalSpatialSquareTwoCrossingHaar H
local notation "C5" => p4Q2PX_originalFifthFourthJetCoefficient H

/-- The genuine centered-spatial-Wilson-square/two-crossing Haar
moment, without any change in the original Wilson reference measure. -/
noncomputable def p4Q2PY7_originalCenteredSquareTwoCrossingHaar
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, (h A)^2 * (Cross A B)^2 ∂haar

local notation "G" => p4Q2PY7_originalCenteredSquareTwoCrossingHaar H

/-- Exact original spatial Wilson-square separation. The entire
right-boundary dependence is in G(B), since PY6 proves that
the complete temporal-crossing-square Haar mean is constant. -/
theorem p4Q2PY7_originalSpatialSquareCrossing_eq_centered
    (B : Cfg) :
    F B =
      ((∫ A : Cfg, w A ∂haar)^2) *
        (∫ A : Cfg, (Cross A B)^2 ∂haar) + G B := by
  let m : ℝ := ∫ A : Cfg, w A ∂haar
  have hW : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hPhi : Continuous (fun A : Cfg => Φ A) :=
    p4Q2PW2_originalAllPlaquetteRealTrace_continuous H
  have hH : Continuous (fun A : Cfg => h A) := by
    have hEq : (fun A : Cfg => h A) =
        (fun A : Cfg => (1 / 2 : ℝ) * Φ A) := by
      funext A
      exact p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A
    rw [hEq]
    exact continuous_const.mul hPhi
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hCont := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hCont
  have hi0 : Integrable
      (fun A : Cfg => (h A)^2 * (Cross A B)^2) haar :=
    ((hH.pow 2).mul (hCross.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiCross : Integrable
      (fun A : Cfg => (Cross A B)^2) haar :=
    (hCross.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable
      (fun A : Cfg => (m^2) * (Cross A B)^2) haar :=
    hiCross.const_mul (m^2)
  have hiHC : Integrable
      (fun A : Cfg => (Cross A B)^2 * h A) haar :=
    ((hCross.pow 2).mul hH).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable
      (fun A : Cfg => (2 * m) * ((Cross A B)^2 * h A)) haar :=
    hiHC.const_mul (2 * m)
  have hAdd :
      (∫ A : Cfg,
        (h A)^2 * (Cross A B)^2 +
          m^2 * (Cross A B)^2 ∂haar) =
      (∫ A : Cfg, (h A)^2 * (Cross A B)^2 ∂haar) +
        m^2 * (∫ A : Cfg, (Cross A B)^2 ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add hi0 hi1)
  have hSub :
      (∫ A : Cfg,
        ((h A)^2 * (Cross A B)^2 + m^2 * (Cross A B)^2) -
          (2 * m) * ((Cross A B)^2 * h A) ∂haar) =
      (∫ A : Cfg,
        (h A)^2 * (Cross A B)^2 +
          m^2 * (Cross A B)^2 ∂haar) -
      (2 * m) * (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub (hi0.add hi1) hi2)
  have hPoint (A : Cfg) :
      (w A)^2 * (Cross A B)^2 =
      ((h A)^2 * (Cross A B)^2 + m^2 * (Cross A B)^2) -
        (2 * m) * ((Cross A B)^2 * h A) := by
    have hCentered :
        h A = m - w A :=
      p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H A
    rw [hCentered]
    ring
  have hZero : (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) = 0 :=
    p4Q2PW3_originalTwoCrossingCenteredHaar_zero H B
  calc
    F B = ∫ A : Cfg,
      ((h A)^2 * (Cross A B)^2 + m^2 * (Cross A B)^2) -
        (2 * m) * ((Cross A B)^2 * h A) ∂haar := by
      unfold p4Q2PY6_originalSpatialSquareTwoCrossingHaar
      apply integral_congr_ae
      filter_upwards with A
      exact hPoint A
    _ = (∫ A : Cfg, (h A)^2 * (Cross A B)^2 ∂haar) +
      m^2 * (∫ A : Cfg, (Cross A B)^2 ∂haar) -
      (2 * m) * (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) := by
      rw [hSub, hAdd]
    _ = m^2 * (∫ A : Cfg, (Cross A B)^2 ∂haar) + G B := by
      rw [hZero]
      dsimp only [p4Q2PY7_originalCenteredSquareTwoCrossingHaar]
      ring

/-- The centered square is exactly a quarter of the squared sum of
ALL genuine spatial SU(2) plaquette characters. -/
theorem p4Q2PY7_originalCenteredSquare_eq_plaquetteTraceSquare
    (B : Cfg) :
    G B = (1 / 4 : ℝ) *
      (∫ A : Cfg, (Φ A)^2 * (Cross A B)^2 ∂haar) := by
  calc
    G B = ∫ A : Cfg,
      (1 / 4 : ℝ) * ((Φ A)^2 * (Cross A B)^2) ∂haar := by
      unfold p4Q2PY7_originalCenteredSquareTwoCrossingHaar
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A]
      ring
    _ = _ := by rw [integral_const_mul]

/-- Genuine fifth Wilson coefficient depends ONLY on the centered
spatial plaquette-square Haar profile G, not the unweighted
Cross^2 sector or any invented nonzero spectral witness. -/
theorem p4Q2PY7_originalFifthCoefficient_eq_centeredSquareMinor
    (A B C : Cfg) :
    C5 A B C =
      (3 / 4 : ℝ) *
        ((a B - a A) * (G C - G A) -
          (a C - a A) * (G B - G A)) := by
  have hDiff (D : Cfg) : F D - F A = G D - G A := by
    rw [p4Q2PY7_originalSpatialSquareCrossing_eq_centered H D,
      p4Q2PY7_originalSpatialSquareCrossing_eq_centered H A,
      p4Q2PY6_originalCrossingSquare_HaarMean_invariant H D,
      p4Q2PY6_originalCrossingSquare_HaarMean_invariant H A]
    ring
  rw [p4Q2PY6_originalFifthCoefficient_eq_spatialSquareMinor H A B C,
    hDiff B, hDiff C]

end OriginalCenteredSquareFifth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalSpatialSquareCrossing_eq_centered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalCenteredSquare_eq_plaquetteTraceSquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalFifthCoefficient_eq_centeredSquareMinor
