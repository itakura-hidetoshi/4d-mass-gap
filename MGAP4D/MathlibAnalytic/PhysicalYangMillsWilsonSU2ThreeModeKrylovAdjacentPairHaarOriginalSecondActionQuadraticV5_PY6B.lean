import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCrossingSecondMomentInvariantV5_PY6
import Mathlib.Tactic

/-!
# P4-Q2-PY6B — exact quadratic second-action Haar moment in original SU(2)

The TRUE one-slab action S(X,B)=w(X)+Cross(X,B)+w(B)
retains the complete left and right spatial plaquette halfweights.
The original full spatial Haar measure has boundary-independent
Cross and Cross² means by IX and PY6, while the W(X)-weighted
single crossing Haar is constant by the physical gauge Ward lemma PL.

Therefore the genuine second moment is EXACTLY monic quadratic
b(B)=w(B)^2+2 alpha_H w(B)+theta_H
with alpha_H and theta_H explicit original spatial Haar integrals.
No interacting posterior is factorized and no new axiom, sorry,
admit, spectral surrogate or nonzero Wilson coefficient is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY6B_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY6B_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY6B_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY6B_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY6B_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section GenuineSecondActionQuadratic
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H

noncomputable def p4Q2PY6_originalSecondActionLinearScalar : ℝ :=
  (∫ A : Cfg, w A ∂haar) +
    (∫ A : Cfg, Cross A (fun _ => 1) ∂haar)

noncomputable def p4Q2PY6_originalSecondActionConstant : ℝ :=
  (∫ A : Cfg, (w A)^2 ∂haar) +
    2 * (∫ A : Cfg, w A * Cross A (fun _ => 1) ∂haar) +
      (∫ A : Cfg, (Cross A (fun _ => 1))^2 ∂haar)

local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H

private theorem p4Q2PY6B_half_continuous :
    Continuous (fun A : Cfg => w A) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PY6B_cross_continuous (B : Cfg) :
    Continuous (fun A : Cfg => Cross A B) := by
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hc

/-- The original left-half-plus-crossing first Haar integral has an
exact right-boundary-independent value. -/
private theorem p4Q2PY6B_leftStrippedFirstHaar (B : Cfg) :
    (∫ A : Cfg, w A + Cross A B ∂haar) = α := by
  have hw := p4Q2PY6B_half_continuous H
  have hc := p4Q2PY6B_cross_continuous H B
  have hwi : Integrable (fun A : Cfg => w A) haar :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hci : Integrable (fun A : Cfg => Cross A B) haar :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAdd :
      (∫ A : Cfg, w A + Cross A B ∂haar) =
      (∫ A : Cfg, w A ∂haar) +
        (∫ A : Cfg, Cross A B ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hwi hci)
  rw [hAdd, p4Q2IX_originalCrossingAction_HaarMean_eq_identity H B]
  rfl

/-- The genuine Haar integral of (left spatial halfweight + temporal
crossing)^2 is constant in the actual right boundary. -/
private theorem p4Q2PY6B_leftStrippedSquareHaar (B : Cfg) :
    (∫ A : Cfg, (w A + Cross A B)^2 ∂haar) = θ := by
  have hw := p4Q2PY6B_half_continuous H
  have hc := p4Q2PY6B_cross_continuous H B
  have hiW2 : Integrable (fun A : Cfg => (w A)^2) haar :=
    (hw.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiWC : Integrable (fun A : Cfg => w A * Cross A B) haar :=
    (hw.mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiC2 : Integrable (fun A : Cfg => (Cross A B)^2) haar :=
    (hc.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPair : Integrable (fun A : Cfg =>
      (w A)^2 + 2 * (w A * Cross A B)) haar :=
    hiW2.add (hiWC.const_mul 2)
  have hAdd1 :
      (∫ A : Cfg, (w A)^2 + 2 * (w A * Cross A B) ∂haar) =
      (∫ A : Cfg, (w A)^2 ∂haar) +
        2 * (∫ A : Cfg, w A * Cross A B ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add hiW2 (hiWC.const_mul 2))
  have hAdd2 :
      (∫ A : Cfg,
        ((w A)^2 + 2 * (w A * Cross A B)) + (Cross A B)^2 ∂haar) =
      (∫ A : Cfg, (w A)^2 + 2 * (w A * Cross A B) ∂haar) +
        (∫ A : Cfg, (Cross A B)^2 ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hPair hiC2)
  calc
    (∫ A : Cfg, (w A + Cross A B)^2 ∂haar) =
        ∫ A : Cfg,
          ((w A)^2 + 2 * (w A * Cross A B)) + (Cross A B)^2 ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = (∫ A : Cfg, (w A)^2 ∂haar) +
      2 * (∫ A : Cfg, w A * Cross A B ∂haar) +
      (∫ A : Cfg, (Cross A B)^2 ∂haar) := by
      rw [hAdd2, hAdd1]
    _ = θ := by
      rw [p4Q2PY6_originalHalfSpatial_crossingHaar_invariant H B,
        p4Q2PY6_originalCrossingSquare_HaarMean_invariant H B]
      rfl

/-- Exact original SU(2) one-slab SECOND action moment is a monic
quadratic polynomial of right spatial Wilson half-action W(B)/2.
All middle spatial plaquettes remain in the genuine S action. -/
theorem p4Q2PY6_originalSecondActionMoment_quadratic (B : Cfg) :
    b B = (w B)^2 + 2 * α * w B + θ := by
  have hw := p4Q2PY6B_half_continuous H
  have hc := p4Q2PY6B_cross_continuous H B
  let q : Cfg → ℝ := fun A => w A + Cross A B
  have hq : Continuous q := hw.add hc
  have hiq : Integrable q haar :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiq2 : Integrable (fun A : Cfg => (q A)^2) haar :=
    (hq.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiqPlus : Integrable (fun A : Cfg =>
      (q A)^2 + (2 * w B) * q A) haar :=
    hiq2.add (hiq.const_mul (2 * w B))
  have hAdd1 :
      (∫ A : Cfg, (q A)^2 + (2 * w B) * q A ∂haar) =
      (∫ A : Cfg, (q A)^2 ∂haar) +
        (2 * w B) * (∫ A : Cfg, q A ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add hiq2 (hiq.const_mul (2 * w B)))
  have hAdd2 :
      (∫ A : Cfg,
        ((q A)^2 + (2 * w B) * q A) + (w B)^2 ∂haar) =
      (∫ A : Cfg, (q A)^2 + (2 * w B) * q A ∂haar) +
        (w B)^2 := by
    have h := integral_add hiqPlus (integrable_const ((w B)^2))
    simpa [Pi.add_apply] using h
  calc
    b B = (∫ A : Cfg, (S A B)^2 ∂haar) := rfl
    _ = (∫ A : Cfg,
        ((q A)^2 + (2 * w B) * q A) + (w B)^2 ∂haar) := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PS_originalOneSlabAction_rightSplit H A B]
      unfold p4Q2PS_originalRightStrippedAction
      dsimp only [q]
      ring
    _ = (∫ A : Cfg, (q A)^2 ∂haar) +
          (2 * w B) * (∫ A : Cfg, q A ∂haar) +
          (w B)^2 := by
      rw [hAdd2, hAdd1]
    _ = (w B)^2 + 2 * α * w B + θ := by
      rw [show (∫ A : Cfg, (q A)^2 ∂haar) = θ from
        p4Q2PY6B_leftStrippedSquareHaar H B,
        show (∫ A : Cfg, q A ∂haar) = α from
          p4Q2PY6B_leftStrippedFirstHaar H B]
      ring

end GenuineSecondActionQuadratic
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalSecondActionMoment_quadratic
