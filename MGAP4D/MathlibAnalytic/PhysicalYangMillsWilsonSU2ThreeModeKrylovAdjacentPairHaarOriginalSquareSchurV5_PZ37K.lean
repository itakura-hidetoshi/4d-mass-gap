import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPairOverlapGeometryV5_PZ37J
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionSpatialLinkProjectionV5_PZ35D8
import Mathlib.Tactic

/-!
# PZ37K — actual normalized character-square Schur projection

The normalized original character is Tr/2, hence its square has mean 1/4.
Derive the pointwise quaternion square orbit from the existing genuine SU(2)
character-pair identity. Average only by translations of the ORIGINAL full
product Haar. A continuous factor independent of any one genuine plaquette
edge decouples with coefficient 1/4, including both inverse orientations.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "z" => p4Q2PZ35D4_centralMinusOne
local notation "ch" => p4Q2PZ35C_originalOneLinkCharacter
local instance : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact pointwise four-quaternion square identity for the original Tr/2. -/
theorem p4Q2PZ37K_originalCharacter_squareOrbit (u : G) :
    (∑ j : Fin 4, (ch (q j * u))^2) = 1 := by
  have h := p4Q2PZ35D4_originalRealCharacterOrbit (1 : G) u
  simp only [mul_one, p4Q2PZ35D5_originalCharacter_inv, ← pow_two] at h
  have hOne : ch (1 : G) = 1 := by
    unfold p4Q2PZ35C_originalOneLinkCharacter
    rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by decide)]
    norm_num
  exact h.trans hOne

namespace GroundStatePosteriorJoint
section SquareProjection
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- Original product-Haar Schur projection of a square, with an arbitrary
continuous factor independent of the selected true group coordinate. -/
theorem p4Q2PZ37K_originalSpatialHaar_squareProject
    (target : Link) (c : Cfg → G) (F : Cfg → ℝ)
    (hc : Continuous c) (hF : Continuous F)
    (hcInv : ∀ a X, c (T target a X) = c X)
    (hFInv : ∀ a X, F (T target a X) = F X) :
    (∫ X : Cfg, (ch (X target * c X))^2 * F X ∂haar) =
      (1/4 : ℝ) * (∫ X : Cfg, F X ∂haar) := by
  let obs : Cfg → ℝ := fun X => (ch (X target * c X))^2 * F X
  have hcCh : Continuous ch :=
    continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hObs : Continuous obs :=
    ((hcCh.comp ((continuous_apply target).mul hc)).pow 2).mul hF
  have hTerm (a : G) (X : Cfg) :
      obs (T target a X) = (ch (a * (X target * c X)))^2 * F X := by
    dsimp [obs]
    rw [p4Q2PZ35D6_originalLinkTranslate_at H target a X, hcInv a X, hFInv a X]
    simp only [mul_assoc]
  have hOrbit (X : Cfg) :
      (∑ j : Fin 4, (obs (T target (q j) X) + obs (T target (z*q j) X))) =
        2 * F X := by
    simp_rw [hTerm, mul_assoc z, p4Q2PZ35D4_originalCharacter_centralFlip,
      neg_sq]
    calc
      (∑ j : Fin 4,
        ((ch (q j * (X target * c X)))^2 * F X +
         (ch (q j * (X target * c X)))^2 * F X)) =
          2 * (∑ j : Fin 4, (ch (q j * (X target * c X)))^2) * F X := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 2 * F X := by rw [p4Q2PZ37K_originalCharacter_squareOrbit]; ring
  have hAvg := p4Q2PZ35D8_originalSpatialHaar_eightLinkIntegralAverage H target obs hObs
  have hEq : (∫ X : Cfg, (∑ j : Fin 4,
      (obs (T target (q j) X) + obs (T target (z*q j) X))) ∂haar) =
      2 * (∫ X : Cfg, F X ∂haar) := by
    calc
      _ = ∫ X : Cfg, 2 * F X ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        exact hOrbit X
      _ = _ := integral_const_mul _ _
  rw [hEq] at hAvg
  change (∫ X : Cfg, obs X ∂haar) = _
  linarith

/-- The same original square projector for an inverse-oriented link. -/
theorem p4Q2PZ37K_originalSpatialHaar_inverseSquareProject
    (target : Link) (c : Cfg → G) (F : Cfg → ℝ)
    (hc : Continuous c) (hF : Continuous F)
    (hcInv : ∀ a X, c (T target a X) = c X)
    (hFInv : ∀ a X, F (T target a X) = F X) :
    (∫ X : Cfg, (ch ((X target)⁻¹ * c X))^2 * F X ∂haar) =
      (1/4 : ℝ) * (∫ X : Cfg, F X ∂haar) := by
  simp_rw [p4Q2PZ35D7_originalInverseCharacter_as_forward]
  exact p4Q2PZ37K_originalSpatialHaar_squareProject H target
    (fun X => (c X)⁻¹) F hc.inv hF (by intro a X; rw [hcInv a X]) hFInv

/-- Cyclicity lets either projector act inside a genuine noncommutative word. -/
private theorem square_word_rotate (a u b : G) :
    ch (a*u*b) = ch (u*(b*a)) := by
  rw [mul_assoc, p4Q2PZ35D5_originalCharacter_mul_comm a (u*b), mul_assoc]

/-- ANY unused original physical edge decouples the plaquette square.
The four true edges are distinct also at H=0; no geometry is assumed. -/
theorem p4Q2PZ37K_originalPlaquetteSquare_freeEdgeProject
    (p : Plaq) (target : Link)
    (hEdge : target = e0 p ∨ target = e1 p ∨ target = e2 p ∨ target = e3 p)
    (F : Cfg → ℝ) (hF : Continuous F)
    (hFInv : ∀ a X, F (T target a X) = F X) :
    (∫ X : Cfg, (χ p X)^2 * F X ∂haar) =
      (1/4 : ℝ) * (∫ X : Cfg, F X ∂haar) := by
  have hn := p4Q2PZ33_originalFourEdges_list_nodup H p
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
    List.nodup_nil, List.not_mem_nil, and_true] at hn
  have h01 : e0 p ≠ e1 p := hn.1.1
  have h02 : e0 p ≠ e2 p := hn.1.2.1
  have h03 : e0 p ≠ e3 p := hn.1.2.2
  have h12 : e1 p ≠ e2 p := hn.2.1.1
  have h13 : e1 p ≠ e3 p := hn.2.1.2
  have h23 : e2 p ≠ e3 p := hn.2.2
  rcases hEdge with rfl | rfl | rfl | rfl
  · have h := p4Q2PZ37K_originalSpatialHaar_squareProject H (e0 p)
        (fun X => X (e1 p) * (X (e2 p))⁻¹ * (X (e3 p))⁻¹) F
        (by fun_prop) hF (by
          intro a X
          simp only [p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h01.symm,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h02.symm,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h03.symm]) hFInv
    simpa only [p4Q2PV_originalPlaquetteRealCharacter,
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
      p4Q2PZ35C_originalOneLinkCharacter, mul_assoc] using h
  · have h := p4Q2PZ37K_originalSpatialHaar_squareProject H (e1 p)
        (fun X => (X (e2 p))⁻¹ * (X (e3 p))⁻¹ * X (e0 p)) F
        (by fun_prop) hF (by
          intro a X
          simp only [p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h12.symm,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h13.symm,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h01]) hFInv
    convert h using 1
    apply integral_congr_ae
    filter_upwards with X
    change (ch (X (e0 p)*X (e1 p)*(X (e2 p))⁻¹*(X (e3 p))⁻¹))^2*F X = _
    rw [mul_assoc (X (e0 p)*X (e1 p)), square_word_rotate]
    simp only [mul_assoc]
  · have h := p4Q2PZ37K_originalSpatialHaar_inverseSquareProject H (e2 p)
        (fun X => (X (e3 p))⁻¹ * (X (e0 p) * X (e1 p))) F
        (by fun_prop) hF (by
          intro a X
          simp only [p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h23.symm,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h02,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h12]) hFInv
    convert h using 1
    apply integral_congr_ae
    filter_upwards with X
    change (ch ((X (e0 p)*X (e1 p))*(X (e2 p))⁻¹*(X (e3 p))⁻¹))^2*F X = _
    rw [square_word_rotate]
  · have h := p4Q2PZ37K_originalSpatialHaar_inverseSquareProject H (e3 p)
        (fun X => X (e0 p)*X (e1 p)*(X (e2 p))⁻¹) F
        (by fun_prop) hF (by
          intro a X
          simp only [p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h03,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h13,
            p4Q2PZ35D6_originalLinkTranslate_other H _ _ _ h23]) hFInv
    convert h using 1
    apply integral_congr_ae
    filter_upwards with X
    change (ch ((X (e0 p)*X (e1 p)*(X (e2 p))⁻¹)*(X (e3 p))⁻¹))^2*F X = _
    rw [p4Q2PZ35D5_originalCharacter_mul_comm]

end SquareProjection
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37K_originalCharacter_squareOrbit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalSpatialHaar_squareProject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalSpatialHaar_inverseSquareProject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37K_originalPlaquetteSquare_freeEdgeProject
