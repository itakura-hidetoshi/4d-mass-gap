import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthSpatialPolynomialV5_PY5C
import Mathlib.Tactic

/-!
# P4-Q2-PY6 — original SU(2) second crossing Haar and centered spatial moment

Keep the genuine complete spatial SU(2) Haar, full Wilson spatial
plaquette action W, and every temporal crossing plaquette.
Coordinatewise left translation identifies the second crossing moment
at every right boundary with the identity-boundary moment.
The original spatial Wilson weighted crossing has constant Haar mean
by the actual vertex-gauge Ward identity. The centered first Wilson
moment is exactly Haar-mean half-spatial action minus half-spatial action.
These are analytic facts of the original model, not replacement posteriors.
No new axioms, sorry, admit, rank hypothesis, or nonzero witness.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY6_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY6_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY6_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY6_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY6_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY6_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalCrossingSecondHaar
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H

/-- Genuine Haar-invariant second moment of the complete temporal
crossing action, with no assumption of independent Wilson posteriors. -/
theorem p4Q2PY6_originalCrossingSquare_HaarMean_invariant
    (B : Cfg) :
    (∫ A : Cfg, (Cross A B) ^ 2 ∂haar) =
      (∫ A : Cfg, (Cross A (fun _ => 1)) ^ 2 ∂haar) := by
  let T : Cfg → Cfg := fun A e => B e * A e
  let f : Cfg → ℝ := fun A => (Cross A B) ^ 2
  let g : Cfg → ℝ := fun A => (Cross A (fun _ => 1)) ^ 2
  have hPres : MeasurePreserving T haar haar :=
    p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving H B
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCross : Continuous (fun A : Cfg => Cross A B) := by
    have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  have hf : AEStronglyMeasurable f haar :=
    (hCross.pow 2).measurable.aestronglyMeasurable
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf
  calc
    (∫ A : Cfg, (Cross A B) ^ 2 ∂haar) =
        ∫ A : Cfg, f A ∂haar := rfl
    _ = ∫ A : Cfg, f A ∂Measure.map T haar := by rw [hmap]
    _ = ∫ A : Cfg, f (T A) ∂haar :=
      MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
    _ = ∫ A : Cfg, g A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact congrArg (fun z : ℝ => z ^ 2)
        (p4Q2IX_originalCrossingAction_leftTranslate H B A)
    _ = (∫ A : Cfg, (Cross A (fun _ => 1)) ^ 2 ∂haar) := rfl

/-- True W(A)/2-weighted first crossing Haar moment is right-boundary
independent by the already proved gauge Ward symmetry of W. -/
theorem p4Q2PY6_originalHalfSpatial_crossingHaar_invariant (B : Cfg) :
    (∫ A : Cfg, w A * Cross A B ∂haar) =
      (∫ A : Cfg, w A * Cross A (fun _ => 1) ∂haar) := by
  have h :=
    p4Q2PL_originalSpatialWilson_weightedCrossingHaar_invariant H B
  have hScaled := congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) h
  simpa only [p4Q2PS_originalHalfSpatialAction, ← mul_assoc,
    integral_const_mul] using hScaled

/-- The original centered first Wilson action is exactly the
difference between mean spatial half-action and spatial half-action.
This follows from original true SU(2) plaquette trace mean zero. -/
theorem p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half (B : Cfg) :
    h B = (∫ A : Cfg, w A ∂haar) - w B := by
  have hMean :
      (∫ A : Cfg, w A ∂haar) =
        (Fintype.card Plaq : ℝ) / 2 := by
    change (∫ A : Cfg, (1 / 2 : ℝ) * W A ∂haar) =
      (Fintype.card Plaq : ℝ) / 2
    rw [integral_const_mul,
      p4Q2PW2_originalSpatialWilsonAction_HaarMean_eq_card H]
    ring
  calc
    h B = (1 / 2 : ℝ) * Φ B :=
      p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H B
    _ = (Fintype.card Plaq : ℝ) / 2 - w B := by
      rw [p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum H B]
        at *
      unfold p4Q2PS_originalHalfSpatialAction
      rw [p4Q2PW2_originalSpatialWilsonAction_eq_card_sub_traceSum H B]
      ring
    _ = (∫ A : Cfg, w A ∂haar) - w B := by rw [hMean]

end OriginalCrossingSecondHaar
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalCrossingSquare_HaarMean_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalHalfSpatial_crossingHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half
