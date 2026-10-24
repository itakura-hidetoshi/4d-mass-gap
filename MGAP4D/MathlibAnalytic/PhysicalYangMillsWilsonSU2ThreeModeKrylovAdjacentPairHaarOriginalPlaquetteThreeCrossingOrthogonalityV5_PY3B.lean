import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalThreeCrossingFreeLinkV5_PY3
import Mathlib.Tactic

/-!
# P4-Q2-PY3B — true SU(2) plaquette/triple-crossing Haar selection

The center flip of an UNUSED fourth plaquette link preserves any
given three original temporal-crossing energy factors.
The same flip reverses the actual four-edge spatial plaquette trace,
including its inverse-oriented fourth edge.

Original normalized spatial SU(2) Haar invariance therefore proves
the genuine triple-crossing integral is zero. Three crossing link
indices may coincide; no independence or Dobrushin assumption is used.
This is a termwise selection rule for the original Wilson model;
the full sum/cube follows separately. No axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY3B_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY3B_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY3B_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY3B_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY3B_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section TrueOriginalThreeCrossingHaar
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H

/-- Every original SU(2) spatial plaquette character is exactly
orthogonal to EVERY ordered triple of genuine temporal Wilson
crossing energies. All three crossing links can be identical. -/
theorem p4Q2PY3_originalPlaquette_threeCrossingHaar_zero
    (p : Plaq) (e f g : Link) (B : Cfg) :
    (∫ A : Cfg,
      χ p A *
        (E ((A e)⁻¹ * B e) *
          E ((A f)⁻¹ * B f) *
          E ((A g)⁻¹ * B g)) ∂haar) = 0 := by
  obtain ⟨target, hMember, he, hf, hg⟩ :=
    p4Q2PY3_originalPlaquette_freeLink_for_threeCrossings H p e f g
  let obs : Cfg → ℝ := fun A =>
    χ p A *
      (E ((A e)⁻¹ * B e) *
        E ((A f)⁻¹ * B f) *
        E ((A g)⁻¹ * B g))
  have hE (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hObs : Continuous obs :=
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).mul
      (((hE e).mul (hE f)).mul (hE g))
  have hOdd (A : Cfg) : obs (Flip target A) = -obs A := by
    change
      χ p (Flip target A) *
        (E (((Flip target A) e)⁻¹ * B e) *
          E (((Flip target A) f)⁻¹ * B f) *
          E (((Flip target A) g)⁻¹ * B g)) =
      -(χ p A *
        (E ((A e)⁻¹ * B e) *
          E ((A f)⁻¹ * B f) *
          E ((A g)⁻¹ * B g)))
    rw [p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
        H p target hMember A,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target e he.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target f hf.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target g hg.symm A B]
    ring
  change (∫ A : Cfg, obs A ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOdd

end TrueOriginalThreeCrossingHaar
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY3_originalPlaquette_threeCrossingHaar_zero
