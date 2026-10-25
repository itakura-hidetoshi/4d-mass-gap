import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourLinkSecondProjectionV5_PZ35D9B
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D9C — THIRD original SU(2) Haar plaquette-link projection

Apply the PZ35D8 exact original full spatial product Haar projector in
the INVERSE orientation to the third physical plaquette edge e2.
PZ33 pairwise distinctness makes all remaining factors invariant.
The original J_p is now -1/64 times a one-link residual Haar integral,
without replacing the Wilson model or the physical posterior.

No new axiom, sorry, admit, native_decide or unproved Schur premise.
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
local instance p4Q2PZ35D9C_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ35D9C_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ35D9C_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ35D9C_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ35D9C_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ35D9C_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section OriginalThirdEdgeProjection
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

/-- Exactly one physical spatial link remains under the original Haar. -/
noncomputable def p4Q2PZ35D9C_originalOneLinkResidual
    (p : Plaq) (B : Cfg) : ℝ :=
  ∫ A : Cfg,
    χ (B (e0 p) * B (e1 p) * (B (e2 p))⁻¹ * (A (e3 p))⁻¹) *
      E ((A (e3 p))⁻¹ * B (e3 p)) ∂haar

/-- The two-link integral is the inverse-oriented Schur contraction
of edge e2, with the correct SU(2) ordering preserved by trace cyclicity. -/
theorem p4Q2PZ35D9C_originalTwoLinkHaar_thirdEdgeProjection
    (p : Plaq) (B : Cfg) :
    p4Q2PZ35D9B_originalTwoLinkResidual H p B =
      -(1 / 4 : ℝ) * p4Q2PZ35D9C_originalOneLinkResidual H p B := by
  have hn : ([e0 p,e1 p,e2 p,e3 p] : List Link).Nodup :=
    p4Q2PZ33_originalFourEdges_list_nodup H p
  have hTail1 : ([e1 p,e2 p,e3 p] : List Link).Nodup :=
    (List.nodup_cons.mp hn).2
  have hTail2 : ([e2 p,e3 p] : List Link).Nodup :=
    (List.nodup_cons.mp hTail1).2
  have hNot : e2 p ∉ ([e3 p] : List Link) :=
    (List.nodup_cons.mp hTail2).1
  have h32 : e3 p ≠ e2 p := by
    intro h; exact hNot (by simp [h])
  let c : Cfg → G := fun A =>
    (A (e3 p))⁻¹ * B (e0 p) * B (e1 p)
  let F : Cfg → ℝ := fun A =>
    E ((A (e3 p))⁻¹ * B (e3 p))
  have hc : Continuous c := by
    dsimp [c]
    exact ((continuous_apply (e3 p)).inv.mul continuous_const).mul
      continuous_const
  have hF : Continuous F := by
    dsimp [F]
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply (e3 p)).inv.mul continuous_const)
  have hcInv : ∀ (a : G) (A : Cfg), c (T (e2 p) a A) = c A := by
    intro a A
    dsimp [c]
    rw [p4Q2PZ35D6_originalLinkTranslate_other H (e2 p) (e3 p) a h32 A]
  have hFInv : ∀ (a : G) (A : Cfg), F (T (e2 p) a A) = F A := by
    intro a A
    dsimp [F]
    rw [p4Q2PZ35D6_originalLinkTranslate_other H (e2 p) (e3 p) a h32 A]
  have hCyc (A : Cfg) :
      χ (B (e0 p) * B (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹) =
        χ ((A (e2 p))⁻¹ * c A) := by
    dsimp [c]
    calc
      χ (B (e0 p) * B (e1 p) *
          (A (e2 p))⁻¹ * (A (e3 p))⁻¹) =
        χ ((B (e0 p) * B (e1 p)) *
          ((A (e2 p))⁻¹ * (A (e3 p))⁻¹)) := by
          simp only [mul_assoc]
      _ = χ (((A (e2 p))⁻¹ * (A (e3 p))⁻¹) *
          (B (e0 p) * B (e1 p))) :=
        p4Q2PZ35D5_originalCharacter_mul_comm _ _
      _ = χ ((A (e2 p))⁻¹ *
          ((A (e3 p))⁻¹ * B (e0 p) * B (e1 p))) := by
          simp only [mul_assoc]
  have hOut (A : Cfg) :
      χ ((B (e2 p))⁻¹ * c A) =
        χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (A (e3 p))⁻¹) := by
    dsimp [c]
    calc
      χ ((B (e2 p))⁻¹ *
          ((A (e3 p))⁻¹ * B (e0 p) * B (e1 p))) =
        χ (((B (e2 p))⁻¹ * (A (e3 p))⁻¹) *
          (B (e0 p) * B (e1 p))) := by
          simp only [mul_assoc]
      _ = χ ((B (e0 p) * B (e1 p)) *
          ((B (e2 p))⁻¹ * (A (e3 p))⁻¹)) :=
        p4Q2PZ35D5_originalCharacter_mul_comm _ _
      _ = χ (B (e0 p) * B (e1 p) *
          (B (e2 p))⁻¹ * (A (e3 p))⁻¹) := by
          simp only [mul_assoc]
  have hProj :=
    p4Q2PZ35D8_originalSpatialHaar_inverseProject
      H (e2 p) (B (e2 p)) c F hc hF hcInv hFInv
  calc
    p4Q2PZ35D9B_originalTwoLinkResidual H p B =
      (∫ A : Cfg,
        (χ ((A (e2 p))⁻¹ * c A) *
          E ((A (e2 p))⁻¹ * B (e2 p))) * F A ∂haar) := by
        unfold p4Q2PZ35D9B_originalTwoLinkResidual
        apply integral_congr_ae
        filter_upwards with A
        rw [hCyc A]
        dsimp [F]
        ring
    _ = -(1 / 4 : ℝ) * (∫ A : Cfg,
        χ ((B (e2 p))⁻¹ * c A) * F A ∂haar) := hProj
    _ = -(1 / 4 : ℝ) * p4Q2PZ35D9C_originalOneLinkResidual H p B := by
        have hEq :
            (∫ A : Cfg, χ ((B (e2 p))⁻¹ * c A) * F A ∂haar) =
              p4Q2PZ35D9C_originalOneLinkResidual H p B := by
          unfold p4Q2PZ35D9C_originalOneLinkResidual
          apply integral_congr_ae
          filter_upwards with A
          rw [hOut A]
          rfl
        rw [hEq]

/-- The original four-edge Haar integral has contracted THREE genuinely
distinct physical links and is -1/64 times the last original-link
Wilson energy integral. -/
theorem p4Q2PZ35D9C_originalCanonicalHaar_threeEdgeProjection
    (p : Plaq) (B : Cfg) :
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
      -(1 / 64 : ℝ) * p4Q2PZ35D9C_originalOneLinkResidual H p B := by
  calc
    p4Q2PZ34_originalCanonicalFourCrossingHaar H p B =
        (1 / 16 : ℝ) * p4Q2PZ35D9B_originalTwoLinkResidual H p B :=
      p4Q2PZ35D9B_originalCanonicalHaar_twoEdgeProjection H p B
    _ = (1 / 16 : ℝ) *
        (-(1 / 4 : ℝ) * p4Q2PZ35D9C_originalOneLinkResidual H p B) := by
      rw [p4Q2PZ35D9C_originalTwoLinkHaar_thirdEdgeProjection H p B]
    _ = -(1 / 64 : ℝ) * p4Q2PZ35D9C_originalOneLinkResidual H p B := by
      ring

end OriginalThirdEdgeProjection
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9C_originalTwoLinkHaar_thirdEdgeProjection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ35D9C_originalCanonicalHaar_threeEdgeProjection
