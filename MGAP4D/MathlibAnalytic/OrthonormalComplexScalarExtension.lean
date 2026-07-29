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

/-- A literal complex scalar-extension equivalence obtained by matching the
base-changed real orthonormal basis with a complex orthonormal basis. -/
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
        (1 ⊗ₜ[ℝ] bR i) = bC i := by
  change
    ((Algebra.TensorProduct.basis ℂ bR.toBasis).equiv
        bC.toBasis (Equiv.refl ι))
        (1 ⊗ₜ[ℝ] bR.toBasis i) = bC.toBasis i
  rw [← Algebra.TensorProduct.basis_apply (A := ℂ) bR.toBasis i]
  exact Basis.equiv_apply
    (Algebra.TensorProduct.basis ℂ bR.toBasis)
    i bC.toBasis (Equiv.refl ι)

@[simp]
theorem orthonormalComplexScalarExtensionEquiv_tmul_basis
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    (bR : OrthonormalBasis ι ℝ E)
    (bC : OrthonormalBasis ι ℂ F)
    (z : ℂ)
    (i : ι) :
    orthonormalComplexScalarExtensionEquiv bR bC
        (z ⊗ₜ[ℝ] bR i) = z • bC i := by
  calc
    orthonormalComplexScalarExtensionEquiv bR bC
        (z ⊗ₜ[ℝ] bR i) =
      orthonormalComplexScalarExtensionEquiv bR bC
        (z • (1 ⊗ₜ[ℝ] bR i)) := by
          congr 1
          simp [TensorProduct.smul_tmul']
    _ = z • orthonormalComplexScalarExtensionEquiv bR bC
        (1 ⊗ₜ[ℝ] bR i) := by rw [map_smul]
    _ = z • bC i := by
      rw [orthonormalComplexScalarExtensionEquiv_one_tmul_basis]

@[simp]
theorem one_tmul_real_smul
    {E : Type*}
    [AddCommMonoid E]
    [Module ℝ E]
    (r : ℝ)
    (x : E) :
    (1 : ℂ) ⊗ₜ[ℝ] (r • x) = (r : ℂ) ⊗ₜ[ℝ] x := by
  rw [TensorProduct.tmul_smul]
  rw [show r • (1 : ℂ) = (r : ℂ) by
    change (r : ℂ) * 1 = (r : ℂ)
    exact mul_one _]

@[simp]
theorem orthonormalDiagonalLinearMap_apply_basis_scalarExtension
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (i : ι) :
    orthonormalDiagonalLinearMap b a (b i) = a i • b i := by
  change (b.toBasis.constr ℝ (fun j => a j • b j)) (b i) = a i • b i
  simpa using b.toBasis.constr_basis ℝ (fun j => a j • b j) i

@[simp]
theorem orthonormalComplexDiagonalLinearMap_apply_basis_scalarExtension
    {ι F : Type*}
    [Fintype ι]
    [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    (b : OrthonormalBasis ι ℂ F)
    (a : ι → ℝ)
    (i : ι) :
    orthonormalComplexDiagonalLinearMap b a (b i) =
      (a i : ℂ) • b i := by
  change (b.toBasis.constr ℂ (fun j => (a j : ℂ) • b j)) (b i) =
    (a i : ℂ) • b i
  simpa using b.toBasis.constr_basis ℂ (fun j => (a j : ℂ) • b j) i

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
  change
    orthonormalComplexScalarExtensionEquiv bR bC
        ((orthonormalDiagonalLinearMap bR a).baseChange ℂ
          (orthonormalComplexScalarExtensionBasis bR i)) =
      orthonormalComplexDiagonalLinearMap bC a
        (orthonormalComplexScalarExtensionEquiv bR bC
          (orthonormalComplexScalarExtensionBasis bR i))
  rw [show orthonormalComplexScalarExtensionBasis bR i =
      1 ⊗ₜ[ℝ] bR i by
    simp [orthonormalComplexScalarExtensionBasis]]
  rw [LinearMap.baseChange_tmul,
    orthonormalDiagonalLinearMap_apply_basis_scalarExtension,
    one_tmul_real_smul,
    orthonormalComplexScalarExtensionEquiv_tmul_basis,
    orthonormalComplexScalarExtensionEquiv_one_tmul_basis,
    orthonormalComplexDiagonalLinearMap_apply_basis_scalarExtension]

/-- The same identity for the finite-dimensional continuous diagonal
operators, after forgetting continuity. -/
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

/-- A symmetric finite-dimensional real operator is the diagonal operator
reconstructed from its eigenbasis and eigenvalue list. -/
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
  rw [show (hT.eigenvectorBasis hn).toBasis i =
      hT.eigenvectorBasis hn i by rfl]
  rw [hT.apply_eigenvectorBasis hn i]
  exact (orthonormalDiagonalLinearMap_apply_basis_scalarExtension
    (hT.eigenvectorBasis hn) (hT.eigenvalues hn) i).symm

/-- The scalar extension of a symmetric real operator is identified with the
complex diagonal operator carrying the same eigenvalue list. -/
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
  have hdiag := symmetric_eq_orthonormalDiagonalLinearMap T hT hn
  calc
    (orthonormalComplexScalarExtensionEquiv
        (hT.eigenvectorBasis hn) bC).toLinearMap.comp
        (T.baseChange ℂ) =
      (orthonormalComplexScalarExtensionEquiv
        (hT.eigenvectorBasis hn) bC).toLinearMap.comp
        ((orthonormalDiagonalLinearMap
          (hT.eigenvectorBasis hn) (hT.eigenvalues hn)).baseChange ℂ) :=
      congrArg
        (fun S : E →ₗ[ℝ] E =>
          (orthonormalComplexScalarExtensionEquiv
            (hT.eigenvectorBasis hn) bC).toLinearMap.comp
            (S.baseChange ℂ)) hdiag
    _ = (orthonormalComplexDiagonalLinearMap bC (hT.eigenvalues hn)).comp
        (orthonormalComplexScalarExtensionEquiv
          (hT.eigenvectorBasis hn) bC).toLinearMap :=
      orthonormalComplexScalarExtensionEquiv_intertwines_diagonalLinearMap
        (hT.eigenvectorBasis hn) bC (hT.eigenvalues hn)

end

end MathlibAnalytic
end MGAP4D
