import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefectDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Every eigenvalue of an idempotent symmetric positive contraction is exactly
zero or one.  The argument is performed in the canonical Mathlib eigenbasis. -/
theorem eigenvalue_eq_zero_or_one_of_idempotent
    (hIdem : ∀ x : E, D.operator (D.operator x) = D.operator x)
    (i : Fin D.dimension) :
    D.eigenvalue i = 0 ∨ D.eigenvalue i = 1 := by
  have hi := hIdem (D.eigenbasis i)
  rw [D.operator_apply_eigenbasis i, map_smul,
    D.operator_apply_eigenbasis i] at hi
  have hsub :
      D.eigenvalue i • (D.eigenvalue i • D.eigenbasis i) -
          D.eigenvalue i • D.eigenbasis i = 0 :=
    sub_eq_zero.mpr hi
  have hsmul :
      (D.eigenvalue i * D.eigenvalue i - D.eigenvalue i) •
          D.eigenbasis i = 0 := by
    simpa [sub_smul, smul_smul] using hsub
  have hvec : D.eigenbasis i ≠ 0 := by
    have hnorm : ‖D.eigenbasis i‖ = 1 := by simp
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hscalar :
      D.eigenvalue i * D.eigenvalue i - D.eigenvalue i = 0 :=
    (smul_eq_zero.mp hsmul).resolve_right hvec
  have hprod :
      D.eigenvalue i * (D.eigenvalue i - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hone)

/-- For an idempotent symmetric positive contraction, the canonical ground
projector coefficient agrees modewise with the transfer eigenvalue itself. -/
theorem groundSpectralProjectorCoefficient_eq_eigenvalue_of_idempotent
    (hIdem : ∀ x : E, D.operator (D.operator x) = D.operator x)
    (i : Fin D.dimension) :
    D.groundSpectralProjectorCoefficient i = D.eigenvalue i := by
  rcases D.eigenvalue_eq_zero_or_one_of_idempotent hIdem i with hzero | hone
  · simp [groundSpectralProjectorCoefficient, hzero]
  · simp [groundSpectralProjectorCoefficient, hone]

/-- An idempotent symmetric positive contraction is already the orthogonal
spectral projector onto its eigenvalue-one / fixed sector. -/
theorem groundSpectralProjector_eq_operator_of_idempotent
    (hIdem : ∀ x : E, D.operator (D.operator x) = D.operator x) :
    D.groundSpectralProjector = D.operator := by
  apply ContinuousLinearMap.ext
  intro x
  calc
    D.groundSpectralProjector x =
        ∑ i : Fin D.dimension,
          inner ℝ (D.eigenbasis i) x •
            (D.groundSpectralProjectorCoefficient i • D.eigenbasis i) :=
      orthonormalDiagonalOperator_apply
        D.eigenbasis D.groundSpectralProjectorCoefficient x
    _ = ∑ i : Fin D.dimension,
          inner ℝ (D.eigenbasis i) x •
            (D.eigenvalue i • D.eigenbasis i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [D.groundSpectralProjectorCoefficient_eq_eigenvalue_of_idempotent hIdem i]
    _ = D.operator x := (D.operator_apply_eigenbasis_expansion x).symm

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
