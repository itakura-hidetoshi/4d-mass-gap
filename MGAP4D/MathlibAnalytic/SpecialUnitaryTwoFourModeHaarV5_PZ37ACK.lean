import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarOrientationsV5_PZ35D5

/-!
# P4-Q2-PZ37ACK — four genuine SU(2) Haar character coordinates

The four original quaternion elements give four translates of the same real
Wilson character. Their means vanish and their exact Haar Gram matrix is
one quarter the identity. The proof uses the existing compact SU(2) Haar
contraction and the literal quaternion matrices; the measure is unchanged.

These are four coordinate tests for a link receiver. The fixed scalar Wilson
energy is not assumed to be invariant under arbitrary left translation.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "χ" => p4Q2PZ35C_originalOneLinkCharacter
local notation "q" => p4Q2PZ35B_quaternionFamily

local instance p4Q2PZ37ACK_fourModeGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACK_fourModeCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACK_fourModeCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACK_fourModeMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACK_fourModeBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACK_fourModeProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

private theorem p4Q2PZ37ACK_character_continuous : Continuous χ :=
  continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- Four translates by the actual quaternion elements of the original SU(2). -/
def p4Q2PZ37ACK_fourModeCharacter (j : Fin 4) (g : G) : ℝ :=
  χ (q j * g)
local notation "φ" => p4Q2PZ37ACK_fourModeCharacter

/-- Every original coordinate test is continuous on compact SU(2). -/
theorem p4Q2PZ37ACK_fourModeCharacter_continuous (j : Fin 4) :
    Continuous (φ j) :=
  p4Q2PZ37ACK_character_continuous.comp (continuous_const.mul continuous_id)

/-- Coordinate zero is exactly the original scalar Wilson character. -/
theorem p4Q2PZ37ACK_fourModeCharacter_zero (g : G) : φ 0 g = χ g := by
  simp [p4Q2PZ37ACK_fourModeCharacter]

/-- Genuine normalized compact Haar gives mean zero for each coordinate. -/
theorem p4Q2PZ37ACK_fourModeCharacter_mean_zero (j : Fin 4) :
    (∫ g : G, φ j g ∂μ) = 0 := by
  change (∫ g : G, χ (q j * g) ∂μ) = 0
  rw [p4Q2PZ35C_originalSU2Haar_integral_left_translate
    χ p4Q2PZ37ACK_character_continuous (q j),
    p4Q2PZ35D4_originalOneLinkHaar_characterZero]

/-- Two arbitrary left translates of the original character have the exact
compact-Haar correlation dictated by their relative SU(2) element. -/
theorem p4Q2PZ37ACK_originalCharacter_translate_product (a b : G) :
    (∫ g : G, χ (a * g) * χ (b * g) ∂μ) =
      (1 / 4 : ℝ) * χ (a * b⁻¹) := by
  let f : G → ℝ := fun u => χ u * χ (u⁻¹ * (a * b⁻¹))
  have hf : Continuous f :=
    p4Q2PZ37ACK_character_continuous.mul
      (p4Q2PZ37ACK_character_continuous.comp (continuous_id.inv.mul continuous_const))
  have hTranslate (g : G) : f (a * g) = χ (a * g) * χ (b * g) := by
    dsimp [f]
    have hg : (a * g)⁻¹ * (a * b⁻¹) = (b * g)⁻¹ := by group
    rw [hg, p4Q2PZ35D5_originalCharacter_inv]
  calc
    (∫ g : G, χ (a * g) * χ (b * g) ∂μ) = ∫ g : G, f (a * g) ∂μ := by
      apply integral_congr_ae
      filter_upwards with g
      exact (hTranslate g).symm
    _ = ∫ u : G, f u ∂μ :=
      p4Q2PZ35C_originalSU2Haar_integral_left_translate f hf a
    _ = (1 / 4 : ℝ) * χ (a * b⁻¹) :=
      p4Q2PZ35D4_originalOneLinkHaar_characterQuarter (a * b⁻¹)

/-- The literal quaternion matrices have normalized relative character delta. -/
theorem p4Q2PZ37ACK_quaternion_relativeCharacter (i j : Fin 4) :
    χ (q i * (q j)⁻¹) = if i = j then 1 else 0 := by
  have hc : ((χ (q i * (q j)⁻¹) : ℝ) : ℂ) =
      ((if i = j then (1 : ℝ) else 0) : ℂ) := by
    rw [p4Q2PZ35D2_originalCharacter_complex_coe]
    change Matrix.trace (((q i : G) : Mat) * (((q j)⁻¹ : G) : Mat)) / 2 = _
    rw [p4Q2PZ35B_quaternionFamily_coe, p4Q2PZ35D3_quaternionInverse_coe]
    fin_cases i <;> fin_cases j <;>
      norm_num [p4Q2PZ35D3_pauliInverse,
        p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
        p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3,
        Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]
  exact congrArg Complex.re hc

/-- Exact Gram matrix of the four genuine Haar coordinate tests. -/
theorem p4Q2PZ37ACK_fourModeCharacter_gram (i j : Fin 4) :
    (∫ g : G, φ i g * φ j g ∂μ) = if i = j then (1 / 4 : ℝ) else 0 := by
  change (∫ g : G, χ (q i * g) * χ (q j * g) ∂μ) = _
  rw [p4Q2PZ37ACK_originalCharacter_translate_product,
    p4Q2PZ37ACK_quaternion_relativeCharacter]
  split_ifs <;> norm_num

/-- The same four coordinate tests have pointwise squared norm one. -/
theorem p4Q2PZ37ACK_fourModeCharacter_sum_sq (g : G) :
    (∑ j : Fin 4, (φ j g) ^ 2) = 1 := by
  have h := p4Q2PZ35D4_originalRealCharacterOrbit (1 : G) g
  have hOne : χ (1 : G) = 1 := by
    unfold p4Q2PZ35C_originalOneLinkCharacter
    rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
    norm_num
  simpa only [mul_one, p4Q2PZ35D5_originalCharacter_inv, hOne,
    p4Q2PZ37ACK_fourModeCharacter, pow_two] using h

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACK_fourModeCharacter_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACK_fourModeCharacter_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACK_fourModeCharacter_mean_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACK_originalCharacter_translate_product
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACK_quaternion_relativeCharacter
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACK_fourModeCharacter_gram
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACK_fourModeCharacter_sum_sq
