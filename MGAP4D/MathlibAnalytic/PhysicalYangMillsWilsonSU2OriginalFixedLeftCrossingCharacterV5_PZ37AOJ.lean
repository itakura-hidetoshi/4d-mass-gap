import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLocalRelativeTaylorV5_PZ37AOH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOJ — original fixed-left crossing link Haar-character cancellation

For any finite physical even-periodic H, any fixed left original spatial
configuration A and any actual original spatial link e, the genuine
one-link temporal Wilson crossing energy in right configuration B is Haar
orthogonal to the original primary SU(2) character of B.  The proof
uses only ANV's actual Haar-preserving center flips, the two physically
distinct primary origin links, and the original character oddness.
No independent plaquette or alternate probability space is postulated.

This is one conditional crossing *summand* theorem.  It is not yet the
complete fixed-left original action moment, the weighted row response, a
uniform physical top slope, or a Yang--Mills mass-gap theorem.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOJ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOJ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOJ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOJ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOJ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOJ_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The two original positive origin links have distinct native directions
even on the exceptional H=0 spatial length-two torus. -/
theorem p4Q2PZ37AOJ_primaryOriginLinks_ne (H : ℕ) :
    p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ≠
      p4Q2PZ37AMS_primarySpatialSliceEdge H 3 := by
  intro h
  have hEmb :
      (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H) (0 : Fin 4) =
        (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H) (3 : Fin 4) := h
  have hi : (0 : Fin 4) = 3 :=
    (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H).injective hEmb
  exact (by decide : (0 : Fin 4) ≠ 3) hi

/-- An actual single crossing-link term has zero conditional primary-character
Haar pairing for every fixed left boundary A and every original link e. -/
theorem p4Q2PZ37AOJ_originalSingleCrossingEnergy_fixedLeft_primaryCharacter_zero
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let e0 := p4Q2PZ37AMS_primarySpatialSliceEdge H 0
  let e3 := p4Q2PZ37AMS_primarySpatialSliceEdge H 3
  let target : PeriodicHypercubicEvenSpatialSliceLink H :=
    if e = e0 then e3 else e0
  let Flip := GroundStatePosteriorJoint.p4Q2PU_originalSpatialSingleLinkCenterFlip
  have h03 : e0 ≠ e3 := p4Q2PZ37AOJ_primaryOriginLinks_ne H
  have hNot : e ≠ target := by
    by_cases he : e = e0
    · simpa [target, he] using h03
    · simp [target, he]
  have hChoice : target = e0 ∨ target = e3 := by
    by_cases he : e = e0
    · right
      simp [target, he]
    · left
      simp [target, he]
  have hEnergyCont : Continuous (fun B : Cfg =>
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      (continuous_const.mul (continuous_apply e))
  have hChiCont : Continuous (fun B : Cfg =>
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) := by
    have heq :
        (fun B : Cfg =>
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) =
        (fun B => GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
      funext B
      exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
    rw [heq]
    exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous H
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)
  have hCont : Continuous (fun B : Cfg =>
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) :=
    hEnergyCont.mul hChiCont
  have hOdd (B : Cfg) :
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * (Flip H target B) e) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
            (Flip H target B)) =
        -(specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) := by
    dsimp only [Flip]
    rw [GroundStatePosteriorJoint.p4Q2PU_originalSingleLinkCenterFlip_other
        H target e hNot B,
      p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd H target hChoice B]
    ring
  exact GroundStatePosteriorJoint.p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target
    (fun B : Cfg =>
      specialUnitaryWilsonPlaquetteEnergy 2 ((A e)⁻¹ * B e) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B))
    hCont hOdd

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOJ_primaryOriginLinks_ne
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOJ_originalSingleCrossingEnergy_fixedLeft_primaryCharacter_zero
