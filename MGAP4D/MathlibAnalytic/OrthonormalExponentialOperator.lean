import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperator
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

namespace LinearMap.IsSymmetric

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {A : E →ₗ[ℝ] E}

/-- The finite-dimensional exponential functional calculus of a real symmetric
operator, constructed in Mathlib's orthonormal eigenbasis.

At time `t`, the eigenvalue `energy` is sent to `exp (-energy * t)`. -/
noncomputable def exponentialOperator
    (hA : A.IsSymmetric)
    {dimension : ℕ}
    (hFinrank : Module.finrank ℝ E = dimension)
    (t : ℝ) : E →L[ℝ] E :=
  orthonormalDiagonalOperator
    (hA.eigenvectorBasis hFinrank)
    (fun i => Real.exp (-(hA.eigenvalues hFinrank i) * t))

/-- The exponential functional calculus has the expected scalar action on every
Mathlib-generated orthonormal eigenbasis vector. -/
@[simp] theorem exponentialOperator_apply_eigenvectorBasis
    (hA : A.IsSymmetric)
    {dimension : ℕ}
    (hFinrank : Module.finrank ℝ E = dimension)
    (t : ℝ)
    (i : Fin dimension) :
    hA.exponentialOperator hFinrank t
        (hA.eigenvectorBasis hFinrank i) =
      Real.exp (-(hA.eigenvalues hFinrank i) * t) •
        hA.eigenvectorBasis hFinrank i :=
  orthonormalDiagonalOperator_apply_basis
    (hA.eigenvectorBasis hFinrank)
    (fun j => Real.exp (-(hA.eigenvalues hFinrank j) * t))
    i

end LinearMap.IsSymmetric

end

end MathlibAnalytic
end MGAP4D
