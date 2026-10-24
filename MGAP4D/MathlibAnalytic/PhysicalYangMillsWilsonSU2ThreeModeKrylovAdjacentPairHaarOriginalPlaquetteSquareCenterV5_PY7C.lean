import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquettePairFifthV5_PY7B
import Mathlib.Tactic

/-!
# P4-Q2-PY7C — genuine SU(2) spatial plaquette character-square center selection

PY3 proved that the original spatial four-link Wilson plaquette
character changes sign under an actual center flip on ANY of the four
distinct plaquette links. Here show that its SQUARE is invariant
under a single central -I flip at ANY actual spatial link, including
links not contained in that plaquette.

The real original temporal link trace tau_e(A,B)=1-E(A_e⁻¹B_e)
is odd under center flip at e, while every other temporal link trace
is unchanged. Consequently a SINGLE real temporal trace paired
with an original spatial plaquette-character-square has zero Haar
mean, and so does an ordered pair of DISTINCT temporal trace links.

These are true termwise Haar selection rules, not a posterior
factorization or an unproved vanishing assertion about the complete
fifth Ward coefficient or its diagonal crossing-square sector.
No sorry, admit, new axiom, Dobrushin or artificial spectrum.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY7C_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY7C_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY7C_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY7C_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY7C_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section TrueOriginalPlaquetteSquareCenter
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Hol" =>
  periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- For ANY original spatial link, an individual actual SU(2)
plaquette character square is invariant under its central -I flip.
The four true original plaquette links are treated exactly. -/
theorem p4Q2PY7_originalPlaquetteCharSquare_centerEven
    (p : Plaq) (target : Link) (A : Cfg) :
    (χ p (Flip target A))^2 = (χ p A)^2 := by
  by_cases hmem : target = e0 p ∨ target = e1 p ∨
      target = e2 p ∨ target = e3 p
  · rw [p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
      H p target hmem A]
    ring
  · have h0 : e0 p ≠ target := by
      intro h
      exact hmem (Or.inl h.symm)
    have h1 : e1 p ≠ target := by
      intro h
      exact hmem (Or.inr (Or.inl h.symm))
    have h2 : e2 p ≠ target := by
      intro h
      exact hmem (Or.inr (Or.inr (Or.inl h.symm)))
    have h3 : e3 p ≠ target := by
      intro h
      exact hmem (Or.inr (Or.inr (Or.inr h.symm)))
    change
      (1 - E
        (Flip target A (e0 p) * Flip target A (e1 p) *
          (Flip target A (e2 p))⁻¹ *
          (Flip target A (e3 p))⁻¹))^2 =
      (1 - E
        (A (e0 p) * A (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹))^2
    rw [p4Q2PU_originalSingleLinkCenterFlip_other H target (e0 p) h0 A,
      p4Q2PU_originalSingleLinkCenterFlip_other H target (e1 p) h1 A,
      p4Q2PU_originalSingleLinkCenterFlip_other H target (e2 p) h2 A,
      p4Q2PU_originalSingleLinkCenterFlip_other H target (e3 p) h3 A]

/-- The authentic temporal link real trace (one minus its
genuine SU(2) crossing Wilson energy) is ODD under the center
flip of THAT actual spatial source link. -/
theorem p4Q2PY7_originalTemporalLinkTrace_centerOdd
    (e : Link) (A B : Cfg) :
    1 - E (((Flip e A) e)⁻¹ * B e) =
      -(1 - E ((A e)⁻¹ * B e)) := by
  rw [p4Q2PU_originalSingleLinkCenterFlip_at H e A,
    p4Q2PV_originalSU2Center_inverse_mul (A e),
    p4Q2PV_originalSU2Center_move_right ((A e)⁻¹) (B e),
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  ring

/-- A genuine single temporal link trace has ZERO original Haar
pairing with any squared original spatial plaquette character. -/
theorem p4Q2PY7_originalPlaquetteSquare_oneTemporalTrace_Haar_zero
    (p : Plaq) (e : Link) (B : Cfg) :
    (∫ A : Cfg,
      (χ p A)^2 * (1 - E ((A e)⁻¹ * B e)) ∂haar) = 0 := by
  let obs : Cfg → ℝ :=
    fun A => (χ p A)^2 * (1 - E ((A e)⁻¹ * B e))
  have hChi := p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hEnergy : Continuous (fun A : Cfg => E ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hObs : Continuous obs :=
    (hChi.pow 2).mul (continuous_const.sub hEnergy)
  have hOdd (A : Cfg) : obs (Flip e A) = -obs A := by
    dsimp [obs]
    rw [p4Q2PY7_originalPlaquetteCharSquare_centerEven H p e A,
      p4Q2PY7_originalTemporalLinkTrace_centerOdd H e A B]
    ring
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H e obs hObs hOdd

/-- The original spatial plaquette-character-square is orthogonal
under true Haar to ANY two distinct original temporal link
real traces, because flipping the first source link changes only
its temporal character sign. -/
theorem p4Q2PY7_originalPlaquetteSquare_twoDistinctTemporalTraces_Haar_zero
    (p : Plaq) (e f : Link) (hef : e ≠ f) (B : Cfg) :
    (∫ A : Cfg,
      (χ p A)^2 *
        ((1 - E ((A e)⁻¹ * B e)) *
          (1 - E ((A f)⁻¹ * B f))) ∂haar) = 0 := by
  let obs : Cfg → ℝ := fun A =>
    (χ p A)^2 *
      ((1 - E ((A e)⁻¹ * B e)) *
        (1 - E ((A f)⁻¹ * B f)))
  have hChi := p4Q2PV_originalPlaquetteRealCharacter_continuous H p
  have hEnergy (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hObs : Continuous obs :=
    (hChi.pow 2).mul
      ((continuous_const.sub (hEnergy e)).mul
        (continuous_const.sub (hEnergy f)))
  have hOdd (A : Cfg) : obs (Flip e A) = -obs A := by
    dsimp [obs]
    rw [p4Q2PY7_originalPlaquetteCharSquare_centerEven H p e A,
      p4Q2PY7_originalTemporalLinkTrace_centerOdd H e A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H e f hef.symm A B]
    ring
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H e obs hObs hOdd

end TrueOriginalPlaquetteSquareCenter
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalPlaquetteCharSquare_centerEven
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalTemporalLinkTrace_centerOdd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalPlaquetteSquare_oneTemporalTrace_Haar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY7_originalPlaquetteSquare_twoDistinctTemporalTraces_Haar_zero
