import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthWardResidualV5_PY2
import Mathlib.Tactic

/-!
# P4-Q2-PY3 — true spatial plaquette has an unused link for THREE crossings

The four genuine spatial Wilson plaquette edges were shown distinct
in PU3 even at minimal even periodicity. For any THREE original temporal
crossing links, one of the four spatial plaquette edges is untouched.

PV's original center-odd trace proof covers the first three edges.
Here we additionally establish center oddness on the fourth (inverse-
oriented) edge, using the true SU(2) central -I element. This extends
the physical Haar oddness selection rule to any of the four edges.

This does NOT postulate independence of interacting Wilson posteriors,
nonzero fifth coefficients, or a spatial three-point witness.
No sorry, admit, new axiom or substitute spectral measure.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section TrueOriginalPlaquetteFourEdges
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Hol" =>
  periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "z" => specialUnitaryTwoNegativeIdentity

/-- The original four distinct spatial plaquette links cannot all be
occupied by three genuine temporal-crossing links. -/
theorem p4Q2PY3_originalPlaquette_freeLink_for_threeCrossings
    (p : Plaq) (e f g : Link) :
    ∃ target : Link,
      (target = e0 p ∨ target = e1 p ∨
        target = e2 p ∨ target = e3 p) ∧
      target ≠ e ∧ target ≠ f ∧ target ≠ g := by
  obtain ⟨h01, h02, h12⟩ :=
    p4Q2PU3_originalPlaquette_firstThree_distinct H p
  obtain ⟨h30, h31, h32⟩ :=
    p4Q2PU3_originalPlaquette_last_distinct H p
  by_contra hNo
  have hAll (target : Link)
      (hmember : target = e0 p ∨ target = e1 p ∨
        target = e2 p ∨ target = e3 p) :
      target = e ∨ target = f ∨ target = g := by
    by_contra hbad
    have he : target ≠ e := by
      intro ht
      exact hbad (Or.inl ht)
    have hf : target ≠ f := by
      intro ht
      exact hbad (Or.inr (Or.inl ht))
    have hg : target ≠ g := by
      intro ht
      exact hbad (Or.inr (Or.inr ht))
    exact hNo ⟨target, hmember, he, hf, hg⟩
  have h0 : e0 p = e ∨ e0 p = f ∨ e0 p = g :=
    hAll (e0 p) (Or.inl rfl)
  have h1 : e1 p = e ∨ e1 p = f ∨ e1 p = g :=
    hAll (e1 p) (Or.inr (Or.inl rfl))
  have h2 : e2 p = e ∨ e2 p = f ∨ e2 p = g :=
    hAll (e2 p) (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : e3 p = e ∨ e3 p = f ∨ e3 p = g :=
    hAll (e3 p) (Or.inr (Or.inr (Or.inr rfl)))
  rcases h0 with h0 | h0 | h0 <;>
    rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;>
    simp_all

/-- The inverse-oriented FOURTH genuine spatial plaquette edge is
also center odd, proved on the original group-valued four-edge word. -/
theorem p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_edge3
    (p : Plaq) (A : Cfg) :
    χ p (Flip (e3 p) A) = -χ p A := by
  obtain ⟨h30, h31, h32⟩ :=
    p4Q2PU3_originalPlaquette_last_distinct H p
  have hHol : Hol (Flip (e3 p) A) p = Hol A p * z := by
    change
      (Flip (e3 p) A (e0 p)) *
        (Flip (e3 p) A (e1 p)) *
        (Flip (e3 p) A (e2 p))⁻¹ *
        (Flip (e3 p) A (e3 p))⁻¹ =
      (A (e0 p) * A (e1 p) *
        (A (e2 p))⁻¹ * (A (e3 p))⁻¹) * z
    rw [p4Q2PU_originalSingleLinkCenterFlip_other H (e3 p) (e0 p)
        h30.symm A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e3 p) (e1 p)
        h31.symm A,
      p4Q2PU_originalSingleLinkCenterFlip_other H (e3 p) (e2 p)
        h32.symm A,
      p4Q2PU_originalSingleLinkCenterFlip_at H (e3 p) A]
    rw [p4Q2PV_originalSU2Center_inverse_mul (A (e3 p))]
    simp only [mul_assoc]
  unfold p4Q2PV_originalPlaquetteRealCharacter
  rw [hHol, specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  ring

/-- Center-oddness on ALL FOUR genuine links, not only the three
previously needed for the degree-four Ward cancellation. -/
theorem p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
    (p : Plaq) (target : Link)
    (hMember : target = e0 p ∨ target = e1 p ∨
      target = e2 p ∨ target = e3 p)
    (A : Cfg) :
    χ p (Flip target A) = -χ p A := by
  rcases hMember with h0 | h1 | h2 | h3
  · exact p4Q2PV_originalPlaquetteRealCharacter_centerOdd
      H p target (Or.inl h0) A
  · exact p4Q2PV_originalPlaquetteRealCharacter_centerOdd
      H p target (Or.inr (Or.inl h1)) A
  · exact p4Q2PV_originalPlaquetteRealCharacter_centerOdd
      H p target (Or.inr (Or.inr h2)) A
  · subst target
    exact p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_edge3 H p A

end TrueOriginalPlaquetteFourEdges
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY3_originalPlaquette_freeLink_for_threeCrossings
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_edge3
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
