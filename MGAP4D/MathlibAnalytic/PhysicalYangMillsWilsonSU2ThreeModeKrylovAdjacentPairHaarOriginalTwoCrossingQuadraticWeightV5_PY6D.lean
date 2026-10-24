import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthSpatialCancellationV5_PY6C
import Mathlib.Tactic

/-!
# P4-Q2-PY6D — true weighted two-crossing obstruction reduces to spatial-square Haar

The genuine second moment b(B) is monic quadratic in w(B) by PY6B.
The original centered first moment is h(B)=mean(w)-w(B) by PY6.
Consequently the already-proved exact original Wilson Ward weight
 k(A)=2w(A)h(A)-b(A)
is -3*w(A)^2 -2*mean(Cross)*w(A) -theta_H.

PY6/PW3 show (1) genuine unweighted Cross² Haar is independent
of B, (2) weighted w(A)*Cross² Haar is mean(w) times that same
constant. Thus ALL B dependence in the entire true fifth two-crossing
V2(B) is confined to the spatial-square Haar
  F(B)=∫ w(A)^2 Cross(A,B)^2 dHaar(A).

No nonzero/nonaffinity assertion, rank axiom, independent Wilson
posterior, Dobrushin, sorry/admit or substitute spectrum.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY6D_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY6D_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY6D_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY6D_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY6D_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY6D_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalWeightedTwoCrossingQuadratic
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "k" => p4Q2PT_originalSingleCrossingWardWeight H
local notation "V2" => p4Q2PY5_originalWeightedTwoCrossingHaar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H

/-- The original true fifth Ward crossing weight is an EXACT
spatial-Wilson quadratic, not an abstract surrogate test function. -/
theorem p4Q2PY6_originalFifthCrossingWeight_spatialQuadratic (A : Cfg) :
    k A = -3 * (w A)^2 -
      2 * (∫ X : Cfg, Cross X (fun _ => 1) ∂haar) * w A - θ := by
  unfold p4Q2PT_originalSingleCrossingWardWeight
  rw [p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H A,
    p4Q2PY6_originalSecondActionMoment_quadratic H A]
  unfold p4Q2PY6_originalSecondActionLinearScalar
  ring

/-- Original spatial half-action squared paired against the COMPLETE
genuine temporal crossing squared, retaining all plaquette weights. -/
noncomputable def p4Q2PY6_originalSpatialSquareTwoCrossingHaar (B : Cfg) : ℝ :=
  ∫ A : Cfg, (w A)^2 * (Cross A B)^2 ∂haar

local notation "F" => p4Q2PY6_originalSpatialSquareTwoCrossingHaar H

/-- The original w(A)*Cross(A,B)^2 Haar integral is exactly mean(w)
times the ordinary crossing-square Haar integral: PW3 has PROVED
h=mean(w)-w and centered h*Cross² vanishes, for all actual B. -/
theorem p4Q2PY6_originalHalfSpatial_crossingSquare_factor (B : Cfg) :
    (∫ A : Cfg, w A * (Cross A B)^2 ∂haar) =
      (∫ A : Cfg, w A ∂haar) *
        (∫ A : Cfg, (Cross A B)^2 ∂haar) := by
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hp : Continuous (fun A : Cfg => Cross A B) := by
    have hPair : Continuous (fun A : Cfg => (A, B)) :=
      continuous_id.prodMk continuous_const
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hiP : Integrable (fun A : Cfg => (Cross A B)^2) haar :=
    (hp.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiWP : Integrable (fun A : Cfg => w A * (Cross A B)^2) haar :=
    (hw.mul (hp.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSub :
      (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) =
        (∫ X : Cfg, w X ∂haar) *
          (∫ A : Cfg, (Cross A B)^2 ∂haar) -
        (∫ A : Cfg, w A * (Cross A B)^2 ∂haar) := by
    calc
      (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) =
          ∫ A : Cfg,
            (∫ X : Cfg, w X ∂haar) * (Cross A B)^2 -
              w A * (Cross A B)^2 ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        rw [p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H A]
        ring
      _ = (∫ X : Cfg, w X ∂haar) *
          (∫ A : Cfg, (Cross A B)^2 ∂haar) -
        (∫ A : Cfg, w A * (Cross A B)^2 ∂haar) := by
        simpa only [Pi.sub_apply, integral_const_mul] using
          (integral_sub
            (hiP.const_mul (∫ X : Cfg, w X ∂haar)) hiWP)
  have hz := p4Q2PW3_originalTwoCrossingCenteredHaar_zero H B
  change (∫ A : Cfg, (Cross A B)^2 * h A ∂haar) = 0 at hz
  rw [hSub] at hz
  linarith

noncomputable def p4Q2PY6_originalTwoCrossingConstant : ℝ :=
  -(2 * (∫ X : Cfg, Cross X (fun _ => 1) ∂haar) *
      (∫ X : Cfg, w X ∂haar) + θ) *
    (∫ X : Cfg, (Cross X (fun _ => 1))^2 ∂haar)

local notation "κ" => p4Q2PY6_originalTwoCrossingConstant H

/-- The ACTUAL weighted two-crossing Ward contribution equals
-3 times the sole spatial-square two-crossing Haar profile plus
a true reference-Haar constant independent of right boundary. -/
theorem p4Q2PY6_originalWeightedTwoCrossingHaar_eq_spatialSquare
    (B : Cfg) :
    V2 B = -3 * F B + κ := by
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hc : Continuous (fun A : Cfg => Cross A B) := by
    have hPair : Continuous (fun A : Cfg => (A, B)) :=
      continuous_id.prodMk continuous_const
    have hContinuous :=
      (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hContinuous
  have hi0 : Integrable (fun A : Cfg =>
      (w A)^2 * (Cross A B)^2) haar :=
    ((hw.pow 2).mul (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun A : Cfg =>
      w A * (Cross A B)^2) haar :=
    (hw.mul (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun A : Cfg => (Cross A B)^2) haar :=
    (hc.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let t : ℝ := ∫ X : Cfg, Cross X (fun _ => 1) ∂haar
  have hAdd :
      (∫ A : Cfg,
        (-3 : ℝ) * ((w A)^2 * (Cross A B)^2) +
          (-2 * t) * (w A * (Cross A B)^2) ∂haar) =
      -3 * (∫ A : Cfg, (w A)^2 * (Cross A B)^2 ∂haar) +
        (-2 * t) * (∫ A : Cfg, w A * (Cross A B)^2 ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add (hi0.const_mul (-3)) (hi1.const_mul (-2 * t)))
  have hSub :
      (∫ A : Cfg,
        ((-3 : ℝ) * ((w A)^2 * (Cross A B)^2) +
          (-2 * t) * (w A * (Cross A B)^2)) -
          θ * (Cross A B)^2 ∂haar) =
      (∫ A : Cfg,
        (-3 : ℝ) * ((w A)^2 * (Cross A B)^2) +
          (-2 * t) * (w A * (Cross A B)^2) ∂haar) -
        θ * (∫ A : Cfg, (Cross A B)^2 ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub
        ((hi0.const_mul (-3)).add (hi1.const_mul (-2 * t)))
        (hi2.const_mul θ))
  calc
    V2 B =
        ∫ A : Cfg,
          ((-3 : ℝ) * ((w A)^2 * (Cross A B)^2) +
            (-2 * t) * (w A * (Cross A B)^2)) -
            θ * (Cross A B)^2 ∂haar := by
      unfold p4Q2PY5_originalWeightedTwoCrossingHaar
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PY6_originalFifthCrossingWeight_spatialQuadratic H A]
      dsimp only [t]
      ring
    _ = -3 * (∫ A : Cfg, (w A)^2 * (Cross A B)^2 ∂haar) +
        (-2 * t) * (∫ A : Cfg, w A * (Cross A B)^2 ∂haar) -
        θ * (∫ A : Cfg, (Cross A B)^2 ∂haar) := by
      rw [hSub, hAdd]
    _ = -3 * F B + κ := by
      rw [p4Q2PY6_originalHalfSpatial_crossingSquare_factor H B,
        p4Q2PY6_originalCrossingSquare_HaarMean_invariant H B]
      unfold p4Q2PY6_originalSpatialSquareTwoCrossingHaar
        p4Q2PY6_originalTwoCrossingConstant
      dsimp only [t]
      ring

end OriginalWeightedTwoCrossingQuadratic
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalFifthCrossingWeight_spatialQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalHalfSpatial_crossingSquare_factor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalWeightedTwoCrossingHaar_eq_spatialSquare
