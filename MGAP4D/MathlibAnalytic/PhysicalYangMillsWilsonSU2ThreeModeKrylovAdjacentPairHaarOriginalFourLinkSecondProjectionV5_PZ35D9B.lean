import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourLinkFirstProjectionV5_PZ35D9A
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D9B — SECOND actual plaquette-link Schur contraction

The first original positive link was eliminated in D9A. This file
cyclically transports the genuine Wilson plaquette real character to
put the second actual plaquette link in front, and applies the
unconditional original full-product-Haar projector PZ35D8.
All other factors are invariant because the original plaquette's four
links are pairwise distinct even in the smallest periodic volume.

Result: actual J_p is 1/16 times a genuine residual TWO-link Haar
integral. No assumed Schur identity, alternate product measure,
posterior, new axiom, sorry, admit or native_decide.
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
local instance p4Q2PZ35D9B_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ35D9B_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ35D9B_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ35D9B_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ35D9B_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ35D9B_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section OriginalSecondEdgeProjection
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

/-- Actual PZ35D9A three-link Haar residual, still integrated against
the UNMODIFIED whole spatial slice Haar product. -/
noncomputable def p4Q2PZ35D9B_originalThreeLinkResidual
    (p : Plaq) (B : Cfg) : ℝ :=
  ∫ A : Cfg,
    χ (B (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) *
      (E ((A (e1 p))⁻¹ * B (e1 p)) *
       E ((A (e2 p))⁻¹ * B (e2 p)) *
       E ((A (e3 p))⁻¹ * B (e3 p))) ∂haar

/-- Two genuinely unresolved original links remain after the two
positive-edge SU(2) Schur contractions. -/
noncomputable def p4Q2PZ35D9B_originalTwoLinkResidual
    (p : Plaq) (B : Cfg) : ℝ :=
  ∫ A : Cfg,
    χ (B (e0 p) * B (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹) *
      (E ((A (e2 p))⁻¹ * B (e2 p)) *
       E ((A (e3 p))⁻¹ * B (e3 p))) ∂haar

/-- SECOND edge contraction on the actual finite-volume spatial
Haar law. PZ33 certifies this edge differs from all survivors. -/
theorem p4Q2PZ35D9B_originalThreeLinkHaar_secondEdgeProjection
    (p : Plaq) (B : Cfg) :
    p4Q2PZ35D9B_originalThreeLinkResidual H p B =
      -(1 / 4 : ℝ) * p4Q2PZ35D9B_originalTwoLinkResidual H p B := by
  have hn : ([e0 p,e1 p,e2 p,e3 p] : List Link).Nodup :=
    p4Q2PZ33_originalFourEdges_list_nodup H p
  have hTail : ([e1 p,e2 p,e3 p] : List Link).Nodup :=
    (List.nodup_cons.mp hn).2
  have hNot : e1 p ∉ ([e2 p,e3 p] : List Link) :=
    (List.nodup_cons.mp hTail).1
  have h21 : e2 p ≠ e1 p := by
    intro h; exact hNot (by simp [h])
  have h31 : e3 p ≠ e1 p := by
    intro h; exact hNot (by simp [h])
  let c : Cfg → G := fun A =>
    (A (e2 p))⁻¹ * (A (e3 p))⁻¹ * B (e0 p)
  let F : Cfg → ℝ := fun A =>
    E ((A (e2 p))⁻¹ * B (e2 p)) *
      E ((A (e3 p))⁻¹ * B (e3 p))
  have hc : Continuous c := by
    dsimp [c]
    exact ((continuous_apply (e2 p)).inv.mul
      (continuous_apply (e3 p)).inv).mul continuous_const
  have hE (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hF : Continuous F := by
    dsimp [F]
    exact (hE (e2 p)).mul (hE (e3 p))
  have hcInv : ∀ (a : G) (A : Cfg), c (T (e1 p) a A) = c A := by
    intro a A
    dsimp [c]
    rw [p4Q2PZ35D6_originalLinkTranslate_other H (e1 p) (e2 p) a h21 A,
      p4Q2PZ35D6_originalLinkTranslate_other H (e1 p) (e3 p) a h31 A]
  have hFInv : ∀ (a : G) (A : Cfg), F (T (e1 p) a A) = F A := by
    intro a A
    dsimp [F]
    rw [p4Q2PZ35D6_originalLinkTranslate_other H (e1 p) (e2 p) a h21 A,
      p4Q2PZ35D6_originalLinkTranslate_other H (e1 p) (e3 p) a h31 A]
  have hCyc (A : Cfg) :
      χ (B (e0 p) * A (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹) =
        χ (A (e1 p) * c A) := by
    dsimp [c]
    calc
      χ (B (e0 p) * A (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹) =
        χ (B (e0 p) *
          (A (e1 p) * ((A (e2 p))⁻¹ * (A (e3 p))⁻¹))) := by
          simp only [mul_assoc]
      _ = χ ((A (e1 p) * ((A (e2 p))⁻¹ * (A (e3 p))⁻¹)) *
          B (e0 p)) :=
        p4Q2PZ35D5_originalCharacter_mul_comm _ _
      _ = χ (A (e1 p) *
          ((A (e2 p))⁻¹ * (A (e3 p))⁻¹ * B (e0 p))) := by
          simp only [mul_assoc]
  have hOut (A : Cfg) :
      χ (B (e1 p) * c A) =
        χ (B (e0 p) * B (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹) := by
    dsimp [c]
    calc
      χ (B (e1 p) *
          ((A (e2 p))⁻¹ * (A (e3 p))⁻¹ * B (e0 p))) =
        χ ((B (e1 p) *
          ((A (e2 p))⁻¹ * (A (e3 p))⁻¹)) * B (e0 p)) := by
          simp only [mul_assoc]
      _ = χ (B (e0 p) *
          (B (e1 p) * ((A (e2 p))⁻¹ * (A (e3 p))⁻¹))) :=
        p4Q2PZ35D5_originalCharacter_mul_comm _ _
      _ = χ (B (e0 p) * B (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹) := by
          simp only [mul_assoc]
  have hProj :=
    p4Q2PZ35D8_originalSpatialHaar_forwardProject
      H (e1 p) (B (e1 p)) c F hc hF hcInv hFInv
  calc
    p4Q2PZ35D9B_originalThreeLinkResidual H p B =
      (∫ A : Cfg,
        (χ (A (e1 p) * c A) *
          E ((A (e1 p))⁻¹ * B (e1 p))) * F A ∂haar) := by
        unfold p4Q2PZ35D9B_originalThreeLinkResidual
        apply integral_congr_ae
        filter_upwards with A
        rw [hCyc A]
        dsimp [F]
        ring
    _ = -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ (B (e1 p) * c A) * F A ∂haar) := hProj
    _ = -(1 / 4 : ℝ) * p4Q2PZ35D9B_originalTwoLinkResidual H p B := by
        have hEq :
            (∫ A : Cfg, χ (B (e1 p) * c A) * F A ∂haar) =
              p4Q2PZ35D9B_originalTwoLinkResidual H p B := by
          unfold p4Q2PZ35D9B_originalTwoLinkResidual
          apply integral_congr_ae
          filter_upwards with A
          rw [hOut A]
        rw [hEq]

/-- The ORIGINAL J_p is now one sixteenth of the genuine residual
two-link Haar integral. -/
theorem p4Q2PZ35D9B_originalCanonicalHaar_twoEdgeProjection
    (p : Plaq) (B : Cfg) :
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
      (1 / 16 : ℝ) * p4Q2PZ35D9B_originalTwoLinkResidual H p B := by
  calc
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
        -(1 / 4 : ℝ) * p4Q2PZ35D9B_originalThreeLinkResidual H p B := by
      simpa only [p4Q2PZ35D9B_originalThreeLinkResidual] using
        (p4Q2PZ35D9A_originalCanonicalHaar_firstEdgeProjection H p B)
    _ = -(1 / 4 : ℝ) *
        (-(1 / 4 : ℝ) * p4Q2PZ35D9B_originalTwoLinkResidual H p B) := by
      rw [p4Q2PZ35D9B_originalThreeLinkHaar_secondEdgeProjection H p B]
    _ = (1 / 16 : ℝ) * p4Q2PZ35D9B_originalTwoLinkResidual H p B := by
      ring

end OriginalSecondEdgeProjection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9B_originalThreeLinkHaar_secondEdgeProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9B_originalCanonicalHaar_twoEdgeProjection
