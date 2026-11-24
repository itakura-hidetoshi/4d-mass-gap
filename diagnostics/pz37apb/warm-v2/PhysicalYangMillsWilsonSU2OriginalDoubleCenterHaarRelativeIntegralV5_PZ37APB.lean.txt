import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoOriginMixedCenterDifferenceV5_PZ37AOY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APB — double-center original Haar integration

Use the already certified original single-center AOM identity and the
ANV odd character at the other native origin link. Applying the two
identities in succession gives an exact factor four, with the ordered
double twist used in AOY/AOZ. This is on the literal original spatial
Haar space; no independence of plaquettes or change of the model.

The relative integral transport is separately conditional on a
pointwise bound of the form |mixed F - c chi F| <= error F. It is
intended for the exact AOZ kernel estimate after independent
certification. No normalized row slope, gap or continuum conclusion
is asserted by this leaf alone.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "T" => p4Q2PZ37ANV_singleLinkCenterTwist
local notation "E" => p4Q2PZ37AMS_primarySpatialSliceEdge
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy

local instance p4Q2PZ37APB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APB_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APB_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APB_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APB_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APB_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37APB_twist_continuous
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (T H e) := by
  classical
  unfold p4Q2PZ37ANV_singleLinkCenterTwist
  apply continuous_pi
  intro i
  exact (continuous_apply i).mul continuous_const

private theorem p4Q2PZ37APB_character_continuous (H : ℕ) :
    Continuous (fun B : Cfg H 2 => Chi (Hol H 2 B)) := by
  have heq :
      (fun B : Cfg H 2 => Chi (Hol H 2 B)) =
      (fun B => GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
    funext B
    exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
  rw [heq]
  exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
    H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)

/-- Exact double antisymmetrization of the actual Haar row character.
Apply AOM at origin 0 to the difference at origin 3. -/
theorem p4Q2PZ37APB_originalHaarPrimaryCharacter_doubleAntisymmetrization
    (H : ℕ) (F : Cfg H 2 → ℝ) (hF : Continuous F) :
    (∫ B, (F B - F (T H (E H 0) B) - F (T H (E H 3) B) +
        F (T H (E H 3) (T H (E H 0) B))) * Chi (Hol H 2 B) ∂(Mu H 2)) =
      4 * (∫ B, F B * Chi (Hol H 2 B) ∂(Mu H 2)) := by
  let mu := Mu H 2
  let tau0 := T H (E H 0)
  let tau3 := T H (E H 3)
  let chi : Cfg H 2 → ℝ := fun B => Chi (Hol H 2 B)
  let d : Cfg H 2 → ℝ := fun B => F B - F (tau3 B)
  have hChi : Continuous chi := p4Q2PZ37APB_character_continuous H
  have hTau3 : Continuous tau3 := p4Q2PZ37APB_twist_continuous H _
  have hMP : MeasurePreserving tau3 mu mu :=
    p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving H _
  have hOdd (B : Cfg H 2) : chi (tau3 B) = -chi B := by
    change Chi (Hol H 2 (T H (E H 3) B)) = -Chi (Hol H 2 B)
    rw [p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU H (E H 3) B]
    exact p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd H (E H 3) (Or.inr rfl) B
  have hTransport :
      (∫ B, F (tau3 B) * chi (tau3 B) ∂mu) = ∫ B, F B * chi B ∂mu := by
    have hMap :
        (∫ B, F B * chi B ∂Measure.map tau3 mu) =
          ∫ B, F (tau3 B) * chi (tau3 B) ∂mu :=
      integral_map hMP.measurable.aemeasurable (hF.mul hChi).measurable.aestronglyMeasurable
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  have hTwisted : (∫ B, F (tau3 B) * chi B ∂mu) =
      -(∫ B, F B * chi B ∂mu) := by
    have hNeg : (∫ B, F (tau3 B) * chi (tau3 B) ∂mu) =
        -(∫ B, F (tau3 B) * chi B ∂mu) := by
      simp_rw [hOdd, mul_neg]
      rw [integral_neg]
    rw [hNeg] at hTransport
    linarith only [hTransport]
  have hInt : Integrable (fun B => F B * chi B) mu :=
    (hF.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFlipInt : Integrable (fun B => F (tau3 B) * chi B) mu :=
    ((hF.comp hTau3).mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hD : (∫ B, d B * chi B ∂mu) = 2 * ∫ B, F B * chi B ∂mu := by
    calc
      _ = ∫ B, F B * chi B - F (tau3 B) * chi B ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with B
        dsimp [d]
        ring
      _ = (∫ B, F B * chi B ∂mu) - (∫ B, F (tau3 B) * chi B ∂mu) :=
        integral_sub hInt hFlipInt
      _ = _ := by rw [hTwisted]; ring
  have hDCont : Continuous d := hF.sub (hF.comp hTau3)
  have h0 := p4Q2PZ37AOM_originalHaarPrimaryCharacter_antisymmetrization H d hDCont
  change (-2 : ℝ) * (∫ B, d B * chi B ∂mu) =
    -(∫ B, (d B - d (tau0 B)) * chi B ∂mu) at h0
  rw [hD] at h0
  change (∫ B, (F B - F (tau0 B) - F (tau3 B) + F (tau3 (tau0 B))) * chi B ∂mu) =
    4 * (∫ B, F B * chi B ∂mu)
  calc
    _ = ∫ B, (d B - d (tau0 B)) * chi B ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with B
      dsimp [d]
      ring
    _ = _ := by linarith only [h0]

/-- A relative pointwise mixed difference error descends to the exact
original Haar integral with the same relative error constant. -/
theorem p4Q2PZ37APB_originalHaarPrimaryCharacter_mixedRelativeIntegral_abs_le
    (H : ℕ) (F : Cfg H 2 → ℝ) (hF : Continuous F)
    (c err : ℝ) (herr : 0 ≤ err) (hNonneg : ∀ B, 0 ≤ F B)
    (hPoint : ∀ B,
      |F B - F (T H (E H 0) B) - F (T H (E H 3) B) +
        F (T H (E H 3) (T H (E H 0) B)) -
        c * Chi (Hol H 2 B) * F B| ≤ err * F B) :
    |4 * (∫ B, F B * Chi (Hol H 2 B) ∂(Mu H 2)) -
        c * (∫ B, F B * (Chi (Hol H 2 B))^2 ∂(Mu H 2))| ≤
      err * (∫ B, F B ∂(Mu H 2)) := by
  let mu := Mu H 2
  let tau0 := T H (E H 0)
  let tau3 := T H (E H 3)
  let chi : Cfg H 2 → ℝ := fun B => Chi (Hol H 2 B)
  let mixed : Cfg H 2 → ℝ := fun B =>
    F B - F (tau0 B) - F (tau3 B) + F (tau3 (tau0 B))
  let residual : Cfg H 2 → ℝ := fun B => mixed B - c * chi B * F B
  have hChi : Continuous chi := p4Q2PZ37APB_character_continuous H
  have hTau0 : Continuous tau0 := p4Q2PZ37APB_twist_continuous H _
  have hTau3 : Continuous tau3 := p4Q2PZ37APB_twist_continuous H _
  have hMixed : Continuous mixed :=
    ((hF.sub (hF.comp hTau0)).sub (hF.comp hTau3)).add ((hF.comp hTau3).comp hTau0)
  have hRes : Continuous residual := hMixed.sub ((continuous_const.mul hChi).mul hF)
  have hResInt : Integrable (fun B => residual B * chi B) mu :=
    (hRes.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFInt : Integrable F mu :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMixedInt : Integrable (fun B => mixed B * chi B) mu :=
    (hMixed.mul hChi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hQInt : Integrable (fun B => F B * (chi B)^2) mu :=
    (hF.mul (hChi.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hChiAbs (B : Cfg H 2) : |chi B| ≤ 1 := by
    dsimp [chi]
    rw [p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter]
    unfold GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter
    have hlow := specialUnitaryWilsonPlaquetteEnergy_nonneg
      (by norm_num : 0 < (2 : ℕ))
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
    have hup := specialUnitaryWilsonPlaquetteEnergy_le_two
      (by norm_num : 0 < (2 : ℕ))
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
    rw [abs_le]
    constructor <;> linarith only [hlow, hup]
  have hBound (B : Cfg H 2) : ‖residual B * chi B‖ ≤ err * F B := by
    have hP : |residual B| ≤ err * F B := hPoint B
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (err * F B) * |chi B| := mul_le_mul_of_nonneg_right hP (abs_nonneg _)
      _ ≤ (err * F B) * 1 :=
        mul_le_mul_of_nonneg_left (hChiAbs B) (mul_nonneg herr (hNonneg B))
      _ = _ := mul_one _
  have hAnti : (∫ B, mixed B * chi B ∂mu) =
      4 * (∫ B, F B * chi B ∂mu) :=
    p4Q2PZ37APB_originalHaarPrimaryCharacter_doubleAntisymmetrization H F hF
  have hIdentity :
      (∫ B, residual B * chi B ∂mu) =
        4 * (∫ B, F B * chi B ∂mu) - c * (∫ B, F B * (chi B)^2 ∂mu) := by
    calc
      _ = ∫ B, mixed B * chi B - c * (F B * (chi B)^2) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with B
        dsimp [residual]
        ring
      _ = (∫ B, mixed B * chi B ∂mu) -
          (∫ B, c * (F B * (chi B)^2) ∂mu) :=
        integral_sub hMixedInt (hQInt.const_mul c)
      _ = _ := by rw [hAnti, integral_const_mul]
  have hNorm : ‖∫ B, residual B * chi B ∂mu‖ ≤ err * (∫ B, F B ∂mu) := by
    calc
      _ ≤ ∫ B, ‖residual B * chi B‖ ∂mu := norm_integral_le_integral_norm _
      _ ≤ ∫ B, err * F B ∂mu := by
        apply integral_mono_ae hResInt.norm (hFInt.const_mul err)
        filter_upwards [] with B
        exact hBound B
      _ = _ := integral_const_mul _ _
  rw [hIdentity] at hNorm
  simpa only [Real.norm_eq_abs] using hNorm

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APB_originalHaarPrimaryCharacter_doubleAntisymmetrization
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APB_originalHaarPrimaryCharacter_mixedRelativeIntegral_abs_le
