import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionSpatialLinkProjectionV5_PZ35D8
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourEdgeSchurDescentV5_PZ35
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D9A — FIRST actual plaquette-edge projection in original J_p

PZ35D8 proved a single-coordinate projector on the ORIGINAL spatial
product Haar, not a stand-in finite Haar. PZ33 already proved the
four physical plaquette links are pairwise distinct, even for H=0.

Apply the genuine coordinate projector to the first original positive
plaquette edge in the literal PZ25/PZ34 four-crossing integral.
This removes exactly one original Wilson temporal-link energy and
replaces that plaquette group coordinate with the corresponding
original boundary B link, gaining one unconditional factor -1/4.

The remaining three-link projection and the full eigenlaw are not
asserted here. No new axiom, sorry, admit, native_decide, or new model.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

local instance p4Q2PZ35D9A_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance p4Q2PZ35D9A_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2

local instance p4Q2PZ35D9A_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2

local instance p4Q2PZ35D9A_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2

local instance p4Q2PZ35D9A_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ35D9A_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

local instance p4Q2PZ35D9A_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section OriginalFourLinkFirstProjection
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- The genuine original J_p four-edge Haar moment becomes exactly
-1/4 times the original three-edge residual integral. No Schur
eigenlaw is assumed: distinct links come from original PZ33 geometry. -/
theorem p4Q2PZ35D9A_originalCanonicalHaar_firstEdgeProjection
    (p : Plaq) (B : Cfg) :
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
      -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (B (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) *
          (E ((A (e1 p))⁻¹ * B (e1 p)) *
           E ((A (e2 p))⁻¹ * B (e2 p)) *
           E ((A (e3 p))⁻¹ * B (e3 p))) ∂haar) := by
  have hNodup : ([e0 p,e1 p,e2 p,e3 p] : List Link).Nodup :=
    p4Q2PZ33_originalFourEdges_list_nodup H p
  have hn0 : (e0 p) ∉ ([e1 p,e2 p,e3 p] : List Link) :=
    (List.nodup_cons.mp hNodup).1
  have h10 : e1 p ≠ e0 p := by
    intro h
    exact hn0 (by simp [h])
  have h20 : e2 p ≠ e0 p := by
    intro h
    exact hn0 (by simp [h])
  have h30 : e3 p ≠ e0 p := by
    intro h
    exact hn0 (by simp [h])
  let c : Cfg → G := fun A =>
    A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹
  let F : Cfg → ℝ := fun A =>
    E ((A (e1 p))⁻¹ * B (e1 p)) *
      E ((A (e2 p))⁻¹ * B (e2 p)) *
      E ((A (e3 p))⁻¹ * B (e3 p))
  have hc : Continuous c := by
    dsimp [c]
    exact ((continuous_apply (e1 p)).mul
      (continuous_apply (e2 p)).inv).mul (continuous_apply (e3 p)).inv
  have hE (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hF : Continuous F := by
    dsimp [F]
    exact ((hE (e1 p)).mul (hE (e2 p))).mul (hE (e3 p))
  have hcInv : ∀ (a : G) (A : Cfg), c (T (e0 p) a A) = c A := by
    intro a A
    change
      (T (e0 p) a A) (e1 p) *
        ((T (e0 p) a A) (e2 p))⁻¹ *
        ((T (e0 p) a A) (e3 p))⁻¹ =
      A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹
    rw [p4Q2PZ35D6_originalLinkTranslate_other H (e0 p) (e1 p) a h10 A,
      p4Q2PZ35D6_originalLinkTranslate_other H (e0 p) (e2 p) a h20 A,
      p4Q2PZ35D6_originalLinkTranslate_other H (e0 p) (e3 p) a h30 A]
  have hFInv : ∀ (a : G) (A : Cfg), F (T (e0 p) a A) = F A := by
    intro a A
    change
      (E (((T (e0 p) a A) (e1 p))⁻¹ * B (e1 p)) *
       E (((T (e0 p) a A) (e2 p))⁻¹ * B (e2 p)) *
       E (((T (e0 p) a A) (e3 p))⁻¹ * B (e3 p))) =
      (E ((A (e1 p))⁻¹ * B (e1 p)) *
       E ((A (e2 p))⁻¹ * B (e2 p)) *
       E ((A (e3 p))⁻¹ * B (e3 p)))
    rw [p4Q2PZ35D6_originalLinkTranslate_other H (e0 p) (e1 p) a h10 A,
      p4Q2PZ35D6_originalLinkTranslate_other H (e0 p) (e2 p) a h20 A,
      p4Q2PZ35D6_originalLinkTranslate_other H (e0 p) (e3 p) a h30 A]
  have hProj :=
    p4Q2PZ35D8_originalSpatialHaar_forwardProject
      H (e0 p) (B (e0 p)) c F hc hF hcInv hFInv
  calc
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
      (∫ A : Cfg,
        (χ (A (e0 p) * c A) *
          E ((A (e0 p))⁻¹ * B (e0 p))) * F A ∂haar) := by
      unfold p4Q2PZ34_originalCanonicalFourCrossingHaar
        p4Q2PZ25_originalFourCrossingPlaquetteTerm
      apply integral_congr_ae
      filter_upwards with A
      change
        χ (A (e0 p) * A (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹) *
          (E ((A (e0 p))⁻¹ * B (e0 p)) *
           E ((A (e1 p))⁻¹ * B (e1 p)) *
           E ((A (e2 p))⁻¹ * B (e2 p)) *
           E ((A (e3 p))⁻¹ * B (e3 p))) =
        (χ (A (e0 p) * c A) *
          E ((A (e0 p))⁻¹ * B (e0 p))) * F A
      dsimp [c, F]
      simp only [mul_assoc]
    _ = -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (B (e0 p) * c A) * F A ∂haar) := hProj
    _ = -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (B (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) *
          (E ((A (e1 p))⁻¹ * B (e1 p)) *
           E ((A (e2 p))⁻¹ * B (e2 p)) *
           E ((A (e3 p))⁻¹ * B (e3 p))) ∂haar) := by
      dsimp [c, F]
      simp only [mul_assoc]

end OriginalFourLinkFirstProjection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9A_originalCanonicalHaar_firstEdgeProjection
