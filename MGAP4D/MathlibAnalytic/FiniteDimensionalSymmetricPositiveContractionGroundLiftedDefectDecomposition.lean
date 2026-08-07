import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefect
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

/-- Spectral coefficient of the orthogonal projector onto the transfer-fixed
sector.  It is one exactly on eigenvalue-one modes and zero elsewhere. -/
def groundSpectralProjectorCoefficient (i : Fin D.dimension) : ℝ :=
  if D.eigenvalue i = 1 then 1 else 0

/-- Orthogonal spectral projector onto the full transfer-fixed sector.  This is
constructed in the same canonical Mathlib eigenbasis used by the transfer and
the ground-lifted defect. -/
noncomputable def groundSpectralProjector : E →L[ℝ] E :=
  orthonormalDiagonalOperator D.eigenbasis D.groundSpectralProjectorCoefficient

@[simp] theorem groundSpectralProjector_apply_eigenbasis
    (i : Fin D.dimension) :
    D.groundSpectralProjector (D.eigenbasis i) =
      D.groundSpectralProjectorCoefficient i • D.eigenbasis i := by
  exact orthonormalDiagonalOperator_apply_basis
    D.eigenbasis D.groundSpectralProjectorCoefficient i

/-- The ground spectral projector is symmetric. -/
theorem groundSpectralProjector_isSymmetric :
    D.groundSpectralProjector.toLinearMap.IsSymmetric :=
  orthonormalDiagonalOperator_isSymmetric
    D.eigenbasis D.groundSpectralProjectorCoefficient

/-- Every eigenvalue-one mode is fixed by the ground spectral projector. -/
@[simp] theorem groundSpectralProjectorCoefficient_ground
    (i : D.GroundSpectralIndex) :
    D.groundSpectralProjectorCoefficient i.1 = 1 := by
  simp [groundSpectralProjectorCoefficient, i.2]

/-- Every strictly excited mode is annihilated by the ground spectral
projector. -/
@[simp] theorem groundSpectralProjectorCoefficient_excited
    (i : D.ExcitedSpectralIndex) :
    D.groundSpectralProjectorCoefficient i.1 = 0 := by
  simp [groundSpectralProjectorCoefficient, ne_of_lt i.2.2]

/-- Every null mode is annihilated by the ground spectral projector. -/
@[simp] theorem groundSpectralProjectorCoefficient_null
    (i : D.NullSpectralIndex) :
    D.groundSpectralProjectorCoefficient i.1 = 0 := by
  have hne : D.eigenvalue i.1 ≠ 1 := by
    rw [i.2]
    norm_num
  simp [groundSpectralProjectorCoefficient, hne]

/-- The ground-lifted defect coefficient is exactly the ordinary transfer
defect coefficient plus the eigenvalue-one projector coefficient. -/
theorem groundLiftedDefectCoefficient_eq_one_sub_add_groundProjector
    (i : Fin D.dimension) :
    D.groundLiftedDefectCoefficient i =
      (1 - D.eigenvalue i) + D.groundSpectralProjectorCoefficient i := by
  by_cases hi : D.eigenvalue i = 1
  · simp [groundLiftedDefectCoefficient,
      groundSpectralProjectorCoefficient, hi]
  · simp [groundLiftedDefectCoefficient,
      groundSpectralProjectorCoefficient, hi]

/-- The transfer action expanded in its canonical orthonormal eigenbasis. -/
theorem operator_apply_eigenbasis_expansion
    (x : E) :
    D.operator x =
      ∑ i : Fin D.dimension,
        inner ℝ (D.eigenbasis i) x •
          (D.eigenvalue i • D.eigenbasis i) := by
  calc
    D.operator x =
        D.operator
          (∑ i : Fin D.dimension,
            inner ℝ (D.eigenbasis i) x • D.eigenbasis i) := by
      rw [D.eigenbasis.sum_repr' x]
    _ = ∑ i : Fin D.dimension,
        inner ℝ (D.eigenbasis i) x •
          D.operator (D.eigenbasis i) := by
      simp only [map_sum, map_smul]
    _ = ∑ i : Fin D.dimension,
        inner ℝ (D.eigenbasis i) x •
          (D.eigenvalue i • D.eigenbasis i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [D.operator_apply_eigenbasis i]

/-- Exact basis-free decomposition of the ground-lifted defect:

`D_lift = (I - T) + P_ground`.

This isolates the two genuinely geometric cross-volume obligations: transfer
compatibility and compatibility of the transfer-fixed sector. -/
theorem groundLiftedDefect_apply_eq_sub_operator_add_groundSpectralProjector
    (x : E) :
    D.groundLiftedDefect x =
      x - D.operator x + D.groundSpectralProjector x := by
  have hT := D.operator_apply_eigenbasis_expansion x
  have hP :
      D.groundSpectralProjector x =
        ∑ i : Fin D.dimension,
          inner ℝ (D.eigenbasis i) x •
            (D.groundSpectralProjectorCoefficient i • D.eigenbasis i) :=
    orthonormalDiagonalOperator_apply
      D.eigenbasis D.groundSpectralProjectorCoefficient x
  calc
    D.groundLiftedDefect x =
        ∑ i : Fin D.dimension,
          inner ℝ (D.eigenbasis i) x •
            (D.groundLiftedDefectCoefficient i • D.eigenbasis i) :=
      orthonormalDiagonalOperator_apply
        D.eigenbasis D.groundLiftedDefectCoefficient x
    _ =
        (∑ i : Fin D.dimension,
          inner ℝ (D.eigenbasis i) x • D.eigenbasis i) -
        (∑ i : Fin D.dimension,
          inner ℝ (D.eigenbasis i) x •
            (D.eigenvalue i • D.eigenbasis i)) +
        (∑ i : Fin D.dimension,
          inner ℝ (D.eigenbasis i) x •
            (D.groundSpectralProjectorCoefficient i • D.eigenbasis i)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [D.groundLiftedDefectCoefficient_eq_one_sub_add_groundProjector i]
      module
    _ = x - D.operator x + D.groundSpectralProjector x := by
      rw [D.eigenbasis.sum_repr' x, ← hT, ← hP]

/-- Operator-level form of the exact decomposition. -/
theorem groundLiftedDefect_eq_sub_operator_add_groundSpectralProjector :
    D.groundLiftedDefect.toLinearMap =
      LinearMap.id - D.operator.toLinearMap + D.groundSpectralProjector.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact D.groundLiftedDefect_apply_eq_sub_operator_add_groundSpectralProjector x

/-- Audit-visible package recording the canonical ground projector and the
exact transfer-plus-ground decomposition of the lifted defect. -/
structure GroundLiftedDefectDecompositionPackage where
  groundProjector : E →L[ℝ] E
  groundProjector_eq : groundProjector = D.groundSpectralProjector
  groundProjector_symmetric : groundProjector.toLinearMap.IsSymmetric
  coefficientDecomposition : ∀ i,
    D.groundLiftedDefectCoefficient i =
      (1 - D.eigenvalue i) + D.groundSpectralProjectorCoefficient i
  operatorDecomposition : ∀ x,
    D.groundLiftedDefect x = x - D.operator x + groundProjector x

/-- Construct the complete generic ground-lifted defect decomposition receipt. -/
noncomputable def groundLiftedDefectDecompositionPackage :
    D.GroundLiftedDefectDecompositionPackage where
  groundProjector := D.groundSpectralProjector
  groundProjector_eq := rfl
  groundProjector_symmetric := D.groundSpectralProjector_isSymmetric
  coefficientDecomposition :=
    D.groundLiftedDefectCoefficient_eq_one_sub_add_groundProjector
  operatorDecomposition :=
    D.groundLiftedDefect_apply_eq_sub_operator_add_groundSpectralProjector

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
