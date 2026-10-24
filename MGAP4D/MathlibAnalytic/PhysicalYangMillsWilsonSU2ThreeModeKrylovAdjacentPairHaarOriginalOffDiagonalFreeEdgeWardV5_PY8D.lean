import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDiagonalFullCrossingWardV5_PY8C
import Mathlib.Tactic

/-!
# P4-Q2-PY8D — genuine off-diagonal SU(2) plaquette-pair free-link Ward selection

For the ORIGINAL four oriented spatial Wilson edges, a central -I
flip changes χ_p sign if the link lies on p, and leaves χ_q
unchanged if the link lies on none of q's four physical edges.

Consequently, whenever an actual p-only link is different from
two given genuine temporal crossing links, the unmodified reference
spatial-Haar pairing χ_p χ_q E_e E_f vanishes. This does NOT assume
that such a link exists for EVERY distinct pair p≠q; proving the
global finite-even-lattice geometry (especially side length 2)
is the remaining separate task.

The conditional lemma precisely exposes this genuine geometric
obstruction instead of pretending off-diagonal Ward vanishing.
No posterior substitution, Dobrushin, synthetic rank hypothesis,
new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY8D_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY8D_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY8D_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY8D_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY8D_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalOffDiagonalFreeEdgeWard
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- Original χ_q is strictly unchanged by a center flip at a spatial
link outside ALL FOUR of its genuine oriented plaquette edges. -/
theorem p4Q2PY8_originalPlaquetteChar_centerUnchanged_of_freeEdge
    (q : Plaq) (target : Link)
    (hFree : ¬ (target = e0 q ∨ target = e1 q ∨
        target = e2 q ∨ target = e3 q))
    (A : Cfg) :
    χ q (Flip target A) = χ q A := by
  have h0 : e0 q ≠ target := by
    intro heq
    exact hFree (Or.inl heq.symm)
  have h1 : e1 q ≠ target := by
    intro heq
    exact hFree (Or.inr (Or.inl heq.symm))
  have h2 : e2 q ≠ target := by
    intro heq
    exact hFree (Or.inr (Or.inr (Or.inl heq.symm)))
  have h3 : e3 q ≠ target := by
    intro heq
    exact hFree (Or.inr (Or.inr (Or.inr heq.symm)))
  change
    1 - E
      (Flip target A (e0 q) * Flip target A (e1 q) *
        (Flip target A (e2 q))⁻¹ *
        (Flip target A (e3 q))⁻¹) =
    1 - E
      (A (e0 q) * A (e1 q) *
        (A (e2 q))⁻¹ * (A (e3 q))⁻¹)
  rw [p4Q2PU_originalSingleLinkCenterFlip_other H target (e0 q) h0 A,
    p4Q2PU_originalSingleLinkCenterFlip_other H target (e1 q) h1 A,
    p4Q2PU_originalSingleLinkCenterFlip_other H target (e2 q) h2 A,
    p4Q2PU_originalSingleLinkCenterFlip_other H target (e3 q) h3 A]

/-- Unmodified original spatial Haar kills the EXACT coupled
plaquette-character pair times ANY two true temporal crossing energies
whenever the provided ORIGINAL free spatial edge occurs in p alone
and outside both specified temporal crossing links. -/
theorem p4Q2PY8_originalPlaquettePair_twoCrossingHaar_zero_of_freeEdge
    (p q : Plaq) (e f target : Link)
    (hp : target = e0 p ∨ target = e1 p ∨
      target = e2 p ∨ target = e3 p)
    (hq : ¬ (target = e0 q ∨ target = e1 q ∨
      target = e2 q ∨ target = e3 q))
    (he : target ≠ e) (hf : target ≠ f)
    (B : Cfg) :
    (∫ A : Cfg,
      (χ p A * χ q A) *
        (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f)) ∂haar) = 0 := by
  let obs : Cfg → ℝ := fun A =>
    (χ p A * χ q A) *
      (E ((A e)⁻¹ * B e) * E ((A f)⁻¹ * B f))
  have hChi (v : Plaq) :
      Continuous (fun A : Cfg => χ v A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hEnergy (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hObs : Continuous obs :=
    ((hChi p).mul (hChi q)).mul ((hEnergy e).mul (hEnergy f))
  have hOdd (A : Cfg) : obs (Flip target A) = -obs A := by
    dsimp [obs]
    rw [p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
        H p target hp A,
      p4Q2PY8_originalPlaquetteChar_centerUnchanged_of_freeEdge
        H q target hq A,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target e he.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target f hf.symm A B]
    ring
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOdd

end OriginalOffDiagonalFreeEdgeWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquetteChar_centerUnchanged_of_freeEdge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY8_originalPlaquettePair_twoCrossingHaar_zero_of_freeEdge
