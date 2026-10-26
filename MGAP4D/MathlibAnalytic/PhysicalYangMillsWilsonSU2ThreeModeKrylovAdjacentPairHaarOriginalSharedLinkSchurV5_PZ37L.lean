import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDiagonalFourthV5_PZ37K
import Mathlib.Tactic

/-!
# PZ37L — genuine shared-link character-pair and conjugation projectors

All averages below are translations of the original normalized full spatial
SU(2) product Haar. The four quaternion matrices provide pointwise identities,
not a replacement integration measure. Both character remainders and the
continuous weight may depend on every other physical link.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "q" => p4Q2PZ35B_quaternionFamily
local notation "ch" => p4Q2PZ35C_originalOneLinkCharacter
local instance : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- Exact complex 2x2 conjugation twirl, without representation hypotheses. -/
theorem p4Q2PZ37L_complexConjugationTrace (A C : Mat) :
    (∑ j : Fin 4, Matrix.trace
      (p4Q2PZ35D3_pauliInverse j * A * p4Q2PZ35D3_pauliMatrix j * C)) =
      2 * Matrix.trace A * Matrix.trace C := by
  simp [Fin.sum_univ_four, p4Q2PZ35D3_pauliInverse, p4Q2PZ35D3_pauliMatrix,
    p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1, p4Q2PZ35A_pauliQ2,
    p4Q2PZ35A_pauliQ3, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The literal normalized character has conjugation orbit 4 ch(a)ch(b). -/
theorem p4Q2PZ37L_originalCharacter_conjugationOrbit (a b u : G) :
    (∑ j : Fin 4, ch ((q j*u)⁻¹*a*(q j*u)*b)) = 4*ch a*ch b := by
  have hTerm (j : Fin 4) :
      ch ((q j*u)⁻¹*a*(q j*u)*b) = ch ((q j)⁻¹*a*q j*(u*b*u⁻¹)) := by
    have hg : (q j*u)⁻¹*a*(q j*u)*b =
        u⁻¹ * ((q j)⁻¹*a*q j*(u*b*u⁻¹)) * u := by group
    rw [hg, p4Q2PZ35D7_originalCharacter_conjugate]
  simp_rw [hTerm]
  have h := p4Q2PZ37L_complexConjugationTrace (a : Mat) ((u*b*u⁻¹ : G) : Mat)
  have hC : ch (u*b*u⁻¹) = ch b := by
    simpa only [inv_inv] using
      (p4Q2PZ35D7_originalCharacter_conjugate u⁻¹ b)
  apply Complex.ofReal_injective
  push_cast
  simp_rw [p4Q2PZ35D2_originalCharacter_complex_coe]
  have ht (j : Fin 4) :
      Matrix.trace ((((q j)⁻¹*a*q j*(u*b*u⁻¹) : G) : Mat)) =
        Matrix.trace (p4Q2PZ35D3_pauliInverse j * (a : Mat) *
          p4Q2PZ35D3_pauliMatrix j * ((u*b*u⁻¹ : G) : Mat)) := by
    change Matrix.trace (((((q j)⁻¹ : G) : Mat) * (a : Mat) *
      ((q j : G) : Mat)) * ((u*b*u⁻¹ : G) : Mat)) = _
    rw [p4Q2PZ35D3_quaternionInverse_coe, p4Q2PZ35B_quaternionFamily_coe]
    rfl
  simp_rw [ht]
  rw [← Finset.sum_div, h]
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hC
  simp only [p4Q2PZ35D2_originalCharacter_complex_coe] at hc
  linear_combination 4 * (Matrix.trace (a : Mat) / 2) * hc

namespace GroundStatePosteriorJoint
section SharedLink
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "T" => p4Q2PZ35D6_originalSpatialSingleLinkLeftTranslate H

/-- Four genuine coordinate translations, integrated against unchanged Haar. -/
theorem p4Q2PZ37L_originalSpatialHaar_fourLinkAverage
    (target : Link) (F : Cfg → ℝ) (hF : Continuous F) :
    (∫ X : Cfg, (∑ j : Fin 4, F (T target (q j) X)) ∂haar) =
      4 * (∫ X : Cfg, F X ∂haar) := by
  have hInt (j : Fin 4) : Integrable (fun X : Cfg => F (T target (q j) X)) haar :=
    (hF.comp (p4Q2PZ35D8_originalSpatialLinkTranslation_continuous H target (q j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finset_sum _ (fun j _ => hInt j)]
  simp_rw [p4Q2PZ35D6_originalSpatialHaar_oneLinkIntegralLeftTranslate H target _ F hF]
  simp [nsmul_eq_mul]

/-- Actual shared-link Schur contraction, with both remainders variable. -/
theorem p4Q2PZ37L_originalSpatialHaar_pairProject
    (target : Link) (c d : Cfg → G) (F : Cfg → ℝ)
    (hc : Continuous c) (hd : Continuous d) (hF : Continuous F)
    (hcInv : ∀ a X, c (T target a X) = c X)
    (hdInv : ∀ a X, d (T target a X) = d X)
    (hFInv : ∀ a X, F (T target a X) = F X) :
    (∫ X : Cfg, ch (X target*c X)*ch ((X target)⁻¹*d X)*F X ∂haar) =
      (1/4 : ℝ)*(∫ X : Cfg, ch (d X*c X)*F X ∂haar) := by
  let obs : Cfg → ℝ := fun X => ch (X target*c X)*ch ((X target)⁻¹*d X)*F X
  have hch : Continuous ch := continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hObs : Continuous obs :=
    ((hch.comp ((continuous_apply target).mul hc)).mul
      (hch.comp ((continuous_apply target).inv.mul hd))).mul hF
  have hTerm (a : G) (X : Cfg) : obs (T target a X) =
      ch ((a*X target)*c X)*ch ((a*X target)⁻¹*d X)*F X := by
    dsimp [obs]
    rw [p4Q2PZ35D6_originalLinkTranslate_at, hcInv, hdInv, hFInv]
  have hOrbit (X : Cfg) : (∑ j : Fin 4, obs (T target (q j) X)) =
      ch (d X*c X)*F X := by
    simp_rw [hTerm]
    rw [← Finset.sum_mul, p4Q2PZ35D7_originalForwardCharacterPairOrbit]
  have hAvg := p4Q2PZ37L_originalSpatialHaar_fourLinkAverage H target obs hObs
  have hInt : (∫ X : Cfg, (∑ j : Fin 4, obs (T target (q j) X)) ∂haar) =
      ∫ X : Cfg, ch (d X*c X)*F X ∂haar := by
    apply integral_congr_ae
    filter_upwards with X
    exact hOrbit X
  rw [hInt] at hAvg
  change (∫ X : Cfg, obs X ∂haar) = _
  linarith

/-- Actual conjugation Schur contraction of the second shared coordinate. -/
theorem p4Q2PZ37L_originalSpatialHaar_conjugationProject
    (target : Link) (c d : Cfg → G) (F : Cfg → ℝ)
    (hc : Continuous c) (hd : Continuous d) (hF : Continuous F)
    (hcInv : ∀ a X, c (T target a X) = c X)
    (hdInv : ∀ a X, d (T target a X) = d X)
    (hFInv : ∀ a X, F (T target a X) = F X) :
    (∫ X : Cfg, ch ((X target)⁻¹*c X*X target*d X)*F X ∂haar) =
      ∫ X : Cfg, ch (c X)*ch (d X)*F X ∂haar := by
  let obs : Cfg → ℝ := fun X => ch ((X target)⁻¹*c X*X target*d X)*F X
  have hch : Continuous ch := continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  have hObs : Continuous obs := (hch.comp
    ((((continuous_apply target).inv.mul hc).mul (continuous_apply target)).mul hd)).mul hF
  have hTerm (a : G) (X : Cfg) : obs (T target a X) =
      ch ((a*X target)⁻¹*c X*(a*X target)*d X)*F X := by
    dsimp [obs]
    rw [p4Q2PZ35D6_originalLinkTranslate_at, hcInv, hdInv, hFInv]
  have hOrbit (X : Cfg) : (∑ j : Fin 4, obs (T target (q j) X)) =
      4*(ch (c X)*ch (d X)*F X) := by
    simp_rw [hTerm]
    rw [← Finset.sum_mul, p4Q2PZ37L_originalCharacter_conjugationOrbit]
    ring
  have hAvg := p4Q2PZ37L_originalSpatialHaar_fourLinkAverage H target obs hObs
  have hInt : (∫ X : Cfg, (∑ j : Fin 4, obs (T target (q j) X)) ∂haar) =
      4*(∫ X : Cfg, ch (c X)*ch (d X)*F X ∂haar) := by
    calc
      _ = ∫ X : Cfg, 4*(ch (c X)*ch (d X)*F X) ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        exact hOrbit X
      _ = _ := integral_const_mul _ _
  rw [hInt] at hAvg
  change (∫ X : Cfg, obs X ∂haar) = _
  linarith

end SharedLink
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37L_complexConjugationTrace
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37L_originalCharacter_conjugationOrbit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalSpatialHaar_fourLinkAverage
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalSpatialHaar_pairProject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalSpatialHaar_conjugationProject
