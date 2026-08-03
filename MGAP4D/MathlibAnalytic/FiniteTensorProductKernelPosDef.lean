import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators Kronecker

noncomputable section

/-- Recursive tensor-power matrix of a finite local kernel.  The index type at
level `n` is the full configuration space `Fin n → α`. -/
noncomputable def finiteTensorKernelMatrix
    {α : Type} [Fintype α]
    (K : Matrix α α ℝ) :
    (n : ℕ) → Matrix (Fin n → α) (Fin n → α) ℝ
  | 0 => 1
  | n + 1 =>
      (finiteTensorKernelMatrix K n ⊗ₖ K).submatrix
        (Fin.succFunEquiv α n) (Fin.succFunEquiv α n)

/-- The recursive tensor matrix is the pointwise product of the local matrix
entries over all finite coordinates. -/
theorem finiteTensorKernelMatrix_apply
    {α : Type} [Fintype α]
    (K : Matrix α α ℝ)
    (n : ℕ)
    (A B : Fin n → α) :
    finiteTensorKernelMatrix K n A B =
      ∏ i : Fin n, K (A i) (B i) := by
  induction n with
  | zero =>
      simp [finiteTensorKernelMatrix]
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp [finiteTensorKernelMatrix, Matrix.kronecker, ih]

/-- Positive definiteness is stable under arbitrary finite tensor powers. -/
theorem finiteTensorKernelMatrix_posDef
    {α : Type} [Fintype α]
    (K : Matrix α α ℝ)
    (hK : K.PosDef)
    (n : ℕ) :
    (finiteTensorKernelMatrix K n).PosDef := by
  induction n with
  | zero =>
      simpa [finiteTensorKernelMatrix] using
        (Matrix.PosDef.one : (1 : Matrix (Fin 0 → α) (Fin 0 → α) ℝ).PosDef)
  | succ n ih =>
      simpa [finiteTensorKernelMatrix] using
        (ih.kronecker hK).submatrix (Fin.succFunEquiv α n).injective

/-- Reindex a full finite configuration space by the canonical enumeration of
its coordinate type. -/
noncomputable def finiteConfigurationEquivFin
    (I α : Type) [Fintype I] :
    (I → α) ≃ (Fin (Fintype.card I) → α) where
  toFun A j := A ((Fintype.equivFin I).symm j)
  invFun B i := B (Fintype.equivFin I i)
  left_inv A := by
    funext i
    simp
  right_inv B := by
    funext j
    simp

/-- Tensor-product kernel matrix on the full configuration space over an
arbitrary finite coordinate type. -/
noncomputable def finiteProductKernelMatrix
    (I α : Type) [Fintype I] [Fintype α]
    (K : Matrix α α ℝ) :
    Matrix (I → α) (I → α) ℝ :=
  (finiteTensorKernelMatrix K (Fintype.card I)).submatrix
    (finiteConfigurationEquivFin I α) (finiteConfigurationEquivFin I α)

/-- Entry formula for the arbitrary finite product kernel matrix. -/
theorem finiteProductKernelMatrix_apply
    (I α : Type) [Fintype I] [Fintype α]
    (K : Matrix α α ℝ)
    (A B : I → α) :
    finiteProductKernelMatrix I α K A B =
      ∏ i : I, K (A i) (B i) := by
  rw [finiteProductKernelMatrix,
    finiteTensorKernelMatrix_apply]
  simpa [finiteConfigurationEquivFin] using
    (Equiv.prod_comp (Fintype.equivFin I).symm
      (fun i : I => K (A i) (B i)))

/-- Positive definiteness of a local matrix gives positive definiteness of the
complete finite product kernel matrix. -/
theorem finiteProductKernelMatrix_posDef
    (I α : Type) [Fintype I] [Fintype α]
    (K : Matrix α α ℝ)
    (hK : K.PosDef) :
    (finiteProductKernelMatrix I α K).PosDef := by
  unfold finiteProductKernelMatrix
  exact (finiteTensorKernelMatrix_posDef K hK (Fintype.card I)).submatrix
    (finiteConfigurationEquivFin I α).injective

end

end MathlibAnalytic
end MGAP4D
