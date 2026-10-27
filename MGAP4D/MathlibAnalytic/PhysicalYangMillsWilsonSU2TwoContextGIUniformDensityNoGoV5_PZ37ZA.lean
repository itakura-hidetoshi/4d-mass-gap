import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2CenteredPlaquetteHaarCovarianceV5_PZ37ZA
import Mathlib.Tactic

/-!
# PZ37ZA — the original two-context compensated GI density cannot be uniform

For the UNCHANGED original compensated two-context GI minors on all true
spatial plaquettes, the centered-Haar Gram-row bound is at most 24 and
the genuine determinant functional has norm at most 2 E_b^2. Therefore

  Q_{H,b}(e,e',z,z') <= 96 E_b^4

uniformly in H AND in all four context variables. The genuine plaquette
count grows at least as 2(H+1). Hence PZ37Z's particular context-selectable
TWO-CONTEXT compensated Q/N_H criterion is false for every fixed b>=0.
For a varying b_H with the previously postulated common original contrast
ceiling (4 E_{b_H}^2)^2 <= K, the same total Q is at most 6K, again ruling
out the corresponding normalized density criterion.

This does NOT rule out coercivity of the original FULL-LINK integrated GL
mass or the continuum Yang--Mills mass gap. It rules out this specific
bounded-two-row compensated sufficient condition, even after contexts are
reselected at each finite volume. No posterior or source is replaced.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance pz37zaNoGo_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance pz37zaNoGo_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance pz37zaNoGo_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance pz37zaNoGo_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance pz37zaNoGo_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- UNCONDITIONAL upper on the ORIGINAL true total GI local-minor-square
energy for every finite H and every two original Wilson contexts. -/
theorem p4Q2PZ37ZA_originalTwoContextGISquareEnergy_le_ninetySix
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb e e' z z' ≤
      96 * (p4Q2LW_originalHarnackContrastScale b) ^ 4 := by
  have hSynth := finiteRealHilbert_synthesis_sq_le_gram_row_bound
    (p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H) 24
    (p4Q2PZ37ZA_centeredPlaquette_gram_row_le_twentyFour H)
  have h := p4Q2PZ37ZA_originalGISquareEnergy_le_of_centered_synthesis
    H b hb 24 (by norm_num) hSynth e e' z z'
  nlinarith

/-- The fixed-b, TWO-CONTEXT, transfer-compensated normalized U0-style
criterion introduced in PZ37Z is FALSE. This conclusion concerns exactly
that definition, not full-link GL or continuum mass-gap existence. -/
theorem p4Q2PZ37ZA_not_contextSelectableOriginalGIUniformDensity
    (b : ℝ) (hb : 0 ≤ b) :
    ¬ p4Q2PZ37Z_contextSelectableOriginalGIUniformDensity b hb := by
  rintro ⟨ε, hε, hAll⟩
  let C : ℝ := 96 * (p4Q2LW_originalHarnackContrastScale b) ^ 4
  obtain ⟨H, hH⟩ := exists_nat_gt (C / ε)
  obtain ⟨e, e', z, z', hLower⟩ := hAll H
  have hCard : H < p4Q2LP_originalSpatialPlaquetteCount H := by
    have h := pz37zaOriginalSpatialPlaquetteCount_ge_sideLength H
    omega
  have hCardReal : (H : ℝ) < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) := by
    exact_mod_cast hCard
  have hN : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) :=
    lt_of_le_of_lt (Nat.cast_nonneg H) hCardReal
  have hBig : C < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (hH.trans hCardReal)
  have hSmall := (le_div_iff₀ hN).mp hLower
  have hUpper := p4Q2PZ37ZA_originalTwoContextGISquareEnergy_le_ninetySix
    H b hb e e' z z'
  change p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb e e' z z' ≤ C at hUpper
  nlinarith

/-- Even allowing b to vary with H does not save the TWO-CONTEXT normalized
criterion if its previously required common actual Harnack envelope holds. -/
theorem p4Q2PZ37ZA_not_scheduleOriginalGIUniformDensity_of_envelope
    (b : ℕ → ℝ) (hb : ∀ H, 0 ≤ b H) (K : ℝ)
    (hEnvelope : ∀ H,
      (4 * (p4Q2LW_originalHarnackContrastScale (b H)) ^ 2) ^ 2 ≤ K) :
    ¬ p4Q2PZ37Z_scheduleContextSelectableOriginalGIUniformDensity b hb := by
  rintro ⟨ε, hε, hAll⟩
  obtain ⟨H, hH⟩ := exists_nat_gt ((6 * K) / ε)
  obtain ⟨e, e', z, z', hLower⟩ := hAll H
  have hCard : H < p4Q2LP_originalSpatialPlaquetteCount H := by
    have h := pz37zaOriginalSpatialPlaquetteCount_ge_sideLength H
    omega
  have hCardReal : (H : ℝ) < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) := by
    exact_mod_cast hCard
  have hN : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) :=
    lt_of_le_of_lt (Nat.cast_nonneg H) hCardReal
  have hBig : 6 * K < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (hH.trans hCardReal)
  have hSmall := (le_div_iff₀ hN).mp hLower
  have hUpper :
      p4Q2LY_originalCompensatedLocalGISquareEnergy H (b H) (hb H) e e' z z' ≤
        6 * K := by
    calc
      _ ≤ 96 * (p4Q2LW_originalHarnackContrastScale (b H)) ^ 4 :=
        p4Q2PZ37ZA_originalTwoContextGISquareEnergy_le_ninetySix H (b H) (hb H) e e' z z'
      _ = 6 * (4 * (p4Q2LW_originalHarnackContrastScale (b H)) ^ 2) ^ 2 := by ring
      _ ≤ 6 * K := mul_le_mul_of_nonneg_left (hEnvelope H) (by norm_num)
  nlinarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_originalTwoContextGISquareEnergy_le_ninetySix
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_not_contextSelectableOriginalGIUniformDensity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_not_scheduleOriginalGIUniformDensity_of_envelope
