import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperator
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorInverse
import Mathlib.RingTheory.TensorProduct.Free

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Module
open scoped TensorProduct

/-- The canonical complex basis on the literal scalar extension `ℂ ⊗[ℝ] E`
induced by a real orthonormal basis of `E`. -/
noncomputable def orthonormalComplexScalarExtensionBasis
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) :
    Basis ι ℂ (ℂ ⊗[ℝ] E) :=
  Algebra.TensorProduct.basis ℂ b.toBasis

/-- A literal complex scalar-extension equivalence obtained by sending the
base-changed real orthonormal basis to a chosen complex orthonormal basis with
the same index type. -/
noncomputable def orthonormalComplexScalarExtensionEquiv
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    (bR : OrthonormalBasis ι ℝ E)
    (bC : OrthonormalBasis ι ℂ F) :
    (ℂ ⊗[ℝ] E) ≃ₗ[ℂ] F :=
  (orthonormalComplexScalarExtensionBasis bR).equiv bC.toBasis (Equiv.refl ι)

/-- The scalar-extension equivalence sends `1 ⊗ eᵢ` to the corresponding
complex basis vector. -/
@[simp]
theorem orthonormalComplexScalarExtensionEquiv_one_tmul_basis
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    (bR : OrthonormalBasis ι ℝ E)
    (bC : OrthonormalBasis ι ℂ F)
    (i : ι) :
    orthonormalComplexScalarExtensionEquiv bR bC
        (1 ⊗ₜ[ℝ] bR i) =
      bC i := by
  simp [orthonormalComplexScalarExtensionEquiv,
    orthonormalComplexScalarExtensionBasis]

/-- Conversely, each chosen complex basis vector is represented by the pure
tensor `1 ⊗ eᵢ`. -/
@[simp]
theorem orthonormalComplexScalarExtensionEquiv_symm_basis
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    (bR : OrthonormalBasis ι ℝ E)
    (bC : OrthonormalBasis ι ℂ F)
    (i : ι) :
    (orthonormalComplexScalarExtensionEquiv bR bC).symm (bC i) =
      1 ⊗ₜ[ℝ] bR i := by
  apply (orthonormalComplexScalarExtensionEquiv bR bC).injective
  simp

/-- Extension of scalars for a real diagonal operator is intertwined with the
matching complex diagonal operator. -/
theorem orthonormalComplexScalarExtensionEquiv_intertwines_diagonalLinearMap
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    (bR : OrthonormalBasis ι ℝ E)
    (bC : OrthonormalBasis ι ℂ F)
    (a : ι → ℝ) :
    (orthonormalComplexScalarExtensionEquiv bR bC).toLinearMap.comp
        ((orthonormalDiagonalLinearMap bR a).baseChange ℂ) =
      (orthonormalComplexDiagonalLinearMap bC a).comp
        (orthonormalComplexScalarExtensionEquiv bR bC).toLinearMap := by
  apply (orthonormalComplexScalarExtensionBasis bR).ext
  intro i
  simp [orthonormalComplexScalarExtensionBasis,
    orthonormalComplexScalarExtensionEquiv,
    orthonormalDiagonalLinearMap,
    orthonormalComplexDiagonalLinearMap]

/-- Continuous diagonal operators satisfy the same scalar-extension
intertwining identity after forgetting continuity. -/
theorem orthonormalComplexScalarExtensionEquiv_intertwines_diagonalOperator
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F]
    (bR : OrthonormalBasis ι ℝ E)
    (bC : OrthonormalBasis ι ℂ F)
    (a : ι → ℝ) :
    (orthonormalComplexScalarExtensionEquiv bR bC).toLinearMap.comp
        ((orthonormalDiagonalOperator bR a).toLinearMap.baseChange ℂ) =
      (orthonormalComplexDiagonalOperator bC a).toLinearMap.comp
        (orthonormalComplexScalarExtensionEquiv bR bC).toLinearMap := by
  simpa [orthonormalDiagonalOperator, orthonormalComplexDiagonalOperator]
    using orthonormalComplexScalarExtensionEquiv_intertwines_diagonalLinearMap
      bR bC a

/-- A finite-dimensional symmetric real operator is exactly the diagonal
operator reconstructed from its eigenvector basis and eigenvalue list. -/
theorem symmetric_eq_orthonormalDiagonalLinearMap
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ}
    (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) :
    T = orthonormalDiagonalLinearMap
      (hT.eigenvectorBasis hn) (hT.eigenvalues hn) := by
  apply (hT.eigenvectorBasis hn).toBasis.ext
  intro i
  change T (hT.eigenvectorBasis hn i) =
    (hT.eigenvalues hn i) • hT.eigenvectorBasis hn i
  exact hT.apply_eigenvectorBasis hn i

/-- The literal scalar extension of a symmetric real operator is identified
with the complex diagonal operator having the same eigenvalue list. -/
theorem orthonormalComplexScalarExtensionEquiv_intertwines_symmetric
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    {n : ℕ}
    (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (bC : OrthonormalBasis (Fin n) ℂ F) :
    (orthonormalComplexScalarExtensionEquiv
        (hT.eigenvectorBasis hn) bC).toLinearMap.comp
        (T.baseChange ℂ) =
      (orthonormalComplexDiagonalLinearMap bC (hT.eigenvalues hn)).comp
        (orthonormalComplexScalarExtensionEquiv
          (hT.eigenvectorBasis hn) bC).toLinearMap := by
  rw [symmetric_eq_orthonormalDiagonalLinearMap T hT hn]
  exact orthonormalComplexScalarExtensionEquiv_intertwines_diagonalLinearMap
    (hT.eigenvectorBasis hn) bC (hT.eigenvalues hn)

end

end MathlibAnalytic
end MGAP4D
