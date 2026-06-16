import MGAP4D.MathlibAnalytic.OrthonormalEigenactionRayleigh
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The linear operator diagonal in a finite real orthonormal basis with
coefficient function `a`. -/
noncomputable def orthonormalDiagonalLinearMap
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) : E →ₗ[ℝ] E :=
  b.toBasis.constr ℝ (fun i => a i • b i)

/-- In finite dimension, the diagonal linear operator is automatically a
continuous linear operator. -/
noncomputable def orthonormalDiagonalOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (orthonormalDiagonalLinearMap b a)

/-- The constructed diagonal operator has the prescribed action on every
orthonormal basis vector. -/
@[simp]
theorem orthonormalDiagonalOperator_apply_basis
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (i : ι) :
    orthonormalDiagonalOperator b a (b i) = a i • b i := by
  change (b.toBasis.constr ℝ (fun j => a j • b j)) (b i) = a i • b i
  simpa using b.toBasis.constr_basis ℝ (fun j => a j • b j) i

/-- Coordinate formula for the constructed diagonal operator. -/
theorem orthonormalDiagonalOperator_apply
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (x : E) :
    orthonormalDiagonalOperator b a x =
      ∑ i : ι, inner ℝ (b i) x • (a i • b i) := by
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, orthonormalDiagonalOperator_apply_basis]

/-- A real diagonal operator in an orthonormal basis is symmetric. -/
theorem orthonormalDiagonalOperator_isSymmetric
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    (orthonormalDiagonalOperator b a).toLinearMap.IsSymmetric := by
  intro x y
  have hx := orthonormalDiagonalOperator_apply b a x
  have hy := orthonormalDiagonalOperator_apply b a y
  calc
    inner ℝ (orthonormalDiagonalOperator b a x) y =
        inner ℝ
          (∑ i : ι, inner ℝ (b i) x • (a i • b i)) y :=
      congrArg (fun z : E => inner ℝ z y) hx
    _ = ∑ i : ι,
        inner ℝ (b i) x * (a i * inner ℝ (b i) y) := by
      simp only [sum_inner, real_inner_smul_left]
    _ = ∑ i : ι,
        inner ℝ (b i) y * (a i * inner ℝ x (b i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_comm x (b i)]
      ring
    _ = inner ℝ x
        (∑ i : ι, inner ℝ (b i) y • (a i • b i)) := by
      simp only [inner_sum, real_inner_smul_right]
    _ = inner ℝ x (orthonormalDiagonalOperator b a y) :=
      congrArg (fun z : E => inner ℝ x z) hy.symm

/-- Pairing symmetry in the orientation used by the finite Wilson transfer
interfaces. -/
theorem orthonormalDiagonalOperator_pairing_symmetric
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (x y : E) :
    inner ℝ (orthonormalDiagonalOperator b a x) y =
      inner ℝ (orthonormalDiagonalOperator b a y) x := by
  calc
    inner ℝ (orthonormalDiagonalOperator b a x) y =
        inner ℝ x (orthonormalDiagonalOperator b a y) :=
      orthonormalDiagonalOperator_isSymmetric b a x y
    _ = inner ℝ (orthonormalDiagonalOperator b a y) x :=
      real_inner_comm _ _

/-- The Rayleigh expansion of the constructed diagonal operator is derived
from its basis action and symmetry. -/
theorem orthonormalDiagonalOperator_rayleigh
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (x : E) :
    inner ℝ (orthonormalDiagonalOperator b a x) x =
      ∑ i : ι, (inner ℝ (b i) x) ^ 2 * a i :=
  rayleigh_eq_sum_of_orthonormal_eigenaction
    b (orthonormalDiagonalOperator b a) a
    (orthonormalDiagonalOperator_pairing_symmetric b a)
    (orthonormalDiagonalOperator_apply_basis b a) x

end

end MathlibAnalytic
end MGAP4D
