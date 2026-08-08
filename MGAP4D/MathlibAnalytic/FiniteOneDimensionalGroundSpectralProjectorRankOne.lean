import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefectDecomposition
import MGAP4D.MathlibAnalytic.FiniteDimensionalFullGroundExcitationNullDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct BigOperators

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- The canonical ground spectral projector always lands in the transfer-fixed
space. -/
theorem operator_groundSpectralProjector
    (x : E) :
    D.operator (D.groundSpectralProjector x) =
      D.groundSpectralProjector x := by
  unfold groundSpectralProjector
  rw [orthonormalDiagonalOperator_apply]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [D.operator_apply_eigenbasis]
  by_cases h : D.eigenvalue i = 1
  · simp [groundSpectralProjectorCoefficient, h]
  · simp [groundSpectralProjectorCoefficient, h]

/-- Every exact fixed vector is fixed by the canonical ground spectral
projector. -/
theorem groundSpectralProjector_fixed
    (p : E)
    (hpfix : D.operator p = p) :
    D.groundSpectralProjector p = p := by
  unfold groundSpectralProjector
  rw [orthonormalDiagonalOperator_apply]
  conv_rhs => rw [← D.eigenbasis.sum_repr' p]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : D.eigenvalue i = 1
  · simp [groundSpectralProjectorCoefficient, h]
  · have hsym := D.symmetric (D.eigenbasis i) p
    rw [D.operator_apply_eigenbasis, hpfix] at hsym
    simp only [real_inner_smul_left] at hsym
    have hzeroProd :
        (D.eigenvalue i - 1) * inner ℝ (D.eigenbasis i) p = 0 := by
      nlinarith
    have hcoef : inner ℝ (D.eigenbasis i) p = 0 :=
      (mul_eq_zero.mp hzeroProd).resolve_left (sub_ne_zero.mpr h)
    simp [groundSpectralProjectorCoefficient, h, hcoef]

/-- If the fixed space is the line through a nonzero fixed vector `p`, the
canonical spectral projector is exactly the normalized rank-one projector onto
that line.

This theorem removes all dependence on how the canonical eigenbasis varies in
a parameter: once the Perron fixed ray is one-dimensional, the projector is a
basis-free rational expression in one fixed vector. -/
theorem groundSpectralProjector_eq_normalized_rankOne
    (p : E)
    (hpne : p ≠ 0)
    (hpfix : D.operator p = p)
    (hline : ∀ g : E, D.operator g = g → ∃ c : ℝ, g = c • p) :
    D.groundSpectralProjector =
      (inner ℝ p p)⁻¹ • InnerProductSpace.rankOne ℝ p p := by
  apply ContinuousLinearMap.ext
  intro x
  have hPfixed :
      D.operator (D.groundSpectralProjector x) =
        D.groundSpectralProjector x :=
    D.operator_groundSpectralProjector x
  obtain ⟨c, hc⟩ := hline (D.groundSpectralProjector x) hPfixed
  have hpP : D.groundSpectralProjector p = p :=
    D.groundSpectralProjector_fixed p hpfix
  have hsym := D.groundSpectralProjector_isSymmetric p x
  change
    inner ℝ (D.groundSpectralProjector p) x =
      inner ℝ p (D.groundSpectralProjector x) at hsym
  rw [hpP, hc] at hsym
  simp only [real_inner_smul_right] at hsym
  have hppos : 0 < inner ℝ p p := real_inner_self_pos.mpr hpne
  have hcval : c = (inner ℝ p p)⁻¹ * inner ℝ p x := by
    field_simp [ne_of_gt hppos]
    nlinarith
  rw [hc, hcval]
  rw [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply]
  module

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
