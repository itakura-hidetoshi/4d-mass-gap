import MGAP4D.MathlibAnalytic.FiniteRealHilbertGramRowBesselBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIUniformCouplingEnvelopeV5_PZ37Z
import Mathlib.Tactic

/-!
# PZ37ZA — exact original two-context GI determinant functional

The true compensated two-row GI determinant is ONE bounded linear functional
on the existing spatial product-Haar L2 carrier. Its value on the constant
source is zero, and its norm is at most 2 E_b^2, independently of contexts
and finite volume. Consequently its response on an original plaquette is
unchanged by subtracting that plaquette's genuine Haar mean.

The final theorem of this module is CONDITIONAL on the centered-source
synthesis upper bound. The actual Wilson/Haar finite-overlap premise is
not assumed to have been proved merely by defining the functional.
No posterior, physical source or transfer normalization is replaced.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "G" => p4Q2LW_originalTransferCompensatedGIResponse H b hb
local notation "E" => p4Q2LW_originalHarnackContrastScale b

/-- Exact original two-context determinant response on the Haar L2 carrier. -/
noncomputable def p4Q2PZ37ZA_originalTwoContextDeterminantCLM
    (e e' : Link) (z z' : Cfg × Cfg) : Lp ℝ 2 haar →L[ℝ] ℝ :=
  (G e z (L (1 : C(Cfg, ℝ)))) • G e' z' -
    (G e' z' (L (1 : C(Cfg, ℝ)))) • G e z

local notation "D" => p4Q2PZ37ZA_originalTwoContextDeterminantCLM H b hb

/-- The determinant functional annihilates the genuine constant unit. -/
theorem p4Q2PZ37ZA_originalTwoContextDeterminant_unit_zero
    (e e' : Link) (z z' : Cfg × Cfg) :
    D e e' z z' (L (1 : C(Cfg, ℝ))) = 0 := by
  simp only [p4Q2PZ37ZA_originalTwoContextDeterminantCLM,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Uniform bound on the SAME original determinant functional, not a new
observable and not an unproved frame hypothesis. -/
theorem p4Q2PZ37ZA_originalTwoContextDeterminant_norm_le
    (e e' : Link) (z z' : Cfg × Cfg) :
    ‖D e e' z z'‖ ≤ 2 * E ^ 2 := by
  have hE : 0 ≤ E := p4Q2LW_originalHarnackContrastScale_nonneg b hb
  have ha := p4Q2MA_originalCompensatedGI_unit_abs_le_contrast H b hb e z
  have hc := p4Q2MA_originalCompensatedGI_unit_abs_le_contrast H b hb e' z'
  have hG1 := p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast H b hb e z
  have hG2 := p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast H b hb e' z'
  calc
    ‖D e e' z z'‖ ≤
        ‖(G e z (L (1 : C(Cfg, ℝ)))) • G e' z'‖ +
        ‖(G e' z' (L (1 : C(Cfg, ℝ)))) • G e z‖ := norm_sub_le _ _
    _ = |G e z (L (1 : C(Cfg, ℝ)))| * ‖G e' z'‖ +
        |G e' z' (L (1 : C(Cfg, ℝ)))| * ‖G e z‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ E * E + E * E := add_le_add
      (mul_le_mul ha hG2 (norm_nonneg _) hE)
      (mul_le_mul hc hG1 (norm_nonneg _) hE)
    _ = 2 * E ^ 2 := by ring

/-- Original local Wilson source with its actual product-Haar mean removed. -/
noncomputable def p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource
    (p : Plaq) : Lp ℝ 2 haar :=
  L (p4Q2LO_originalLocalPlaquetteContinuous H p) -
    (∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar) •
      L (1 : C(Cfg, ℝ))

/-- Centering does not alter ANY of the original compensated local minors. -/
theorem p4Q2PZ37ZA_originalTwoContextDeterminant_centered_eq_minor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    D e e' z z' (p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H p) =
      p4Q2LW_originalCompensatedLocalGIMinor H b hb e e' z z' p := by
  rw [p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource, map_sub, map_smul,
    p4Q2PZ37ZA_originalTwoContextDeterminant_unit_zero]
  simp only [smul_zero, sub_zero,
    p4Q2PZ37ZA_originalTwoContextDeterminantCLM,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    p4Q2LW_originalCompensatedLocalGIMinor]
  ring

/-- The original total local GI energy has a volume-independent upper IF
the actual centered plaquette synthesis has such an upper. The premise is
explicit; proving the Wilson/Haar covariance premise remains separate. -/
theorem p4Q2PZ37ZA_originalGISquareEnergy_le_of_centered_synthesis
    (B : ℝ) (hB : 0 ≤ B)
    (hSynthesis : ∀ a : Plaq → ℝ,
      ‖∑ p, a p • p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H p‖ ^ 2 ≤
        B * ∑ p, (a p) ^ 2)
    (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb e e' z z' ≤
      4 * B * E ^ 4 := by
  have hBessel := finiteRealHilbert_functional_sq_sum_le_of_synthesis
    (p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H) B hB hSynthesis
    (D e e' z z')
  simp_rw [p4Q2PZ37ZA_originalTwoContextDeterminant_centered_eq_minor] at hBessel
  have hnorm := p4Q2PZ37ZA_originalTwoContextDeterminant_norm_le H b hb e e' z z'
  have hnormSq : ‖D e e' z z'‖ ^ 2 ≤ (2 * E ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg (by positivity : 0 ≤ 2 * E ^ 2) (norm_nonneg _))]
  change (∑ p, (p4Q2LW_originalCompensatedLocalGIMinor H b hb e e' z z' p) ^ 2) ≤ _
  calc
    _ ≤ B * ‖D e e' z z'‖ ^ 2 := hBessel
    _ ≤ B * (2 * E ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hnormSq hB
    _ = 4 * B * E ^ 4 := by ring

end Frozen
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_originalTwoContextDeterminant_unit_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_originalTwoContextDeterminant_norm_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_originalTwoContextDeterminant_centered_eq_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_originalGISquareEnergy_le_of_centered_synthesis
