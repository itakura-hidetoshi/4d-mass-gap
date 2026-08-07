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

/-- Generic cross-carrier residual for the underlying transfer operators. -/
noncomputable def finiteDimensionalTransferIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.operator.toLinearMap.comp J - J.comp Dc.operator.toLinearMap

/-- Generic cross-carrier residual for the eigenvalue-one spectral projectors. -/
noncomputable def finiteDimensionalGroundProjectorIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.groundSpectralProjector.toLinearMap.comp J -
    J.comp Dc.groundSpectralProjector.toLinearMap

/-- Generic cross-carrier residual for the ground-lifted defects. -/
noncomputable def finiteDimensionalGroundLiftedDefectIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.groundLiftedDefect.toLinearMap.comp J -
    J.comp Dc.groundLiftedDefect.toLinearMap

/-- Exact generic cross-carrier reduction:

`R_lift = R_ground - R_transfer`.

The formula is valid for every linear cross-carrier map and does not assume
isometry, compression equality, or either residual vanishing. -/
theorem finiteDimensionalGroundLiftedDefectIntertwiningResidual_decomposition
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    finiteDimensionalGroundLiftedDefectIntertwiningResidualLinearMap Df Dc J =
      finiteDimensionalGroundProjectorIntertwiningResidualLinearMap Df Dc J -
        finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J := by
  apply LinearMap.ext
  intro x
  change
    Df.groundLiftedDefect (J x) - J (Dc.groundLiftedDefect x) =
      (Df.groundSpectralProjector (J x) -
        J (Dc.groundSpectralProjector x)) -
      (Df.operator (J x) - J (Dc.operator x))
  rw [Df.groundLiftedDefect_apply_eq_sub_operator_add_groundSpectralProjector]
  rw [Dc.groundLiftedDefect_apply_eq_sub_operator_add_groundSpectralProjector]
  rw [map_add, map_sub]
  module

/-- Pointwise generic cross-carrier reduction. -/
theorem finiteDimensionalGroundLiftedDefectIntertwiningResidual_decomposition_apply
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (x : Ec) :
    finiteDimensionalGroundLiftedDefectIntertwiningResidualLinearMap Df Dc J x =
      finiteDimensionalGroundProjectorIntertwiningResidualLinearMap Df Dc J x -
        finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J x := by
  exact LinearMap.congr_fun
    (finiteDimensionalGroundLiftedDefectIntertwiningResidual_decomposition Df Dc J) x

/-- Separate transfer and ground-projector compatibility is sufficient for
exact lifted-defect compatibility.  The converse is intentionally not stated:
nonzero residuals may cancel in the exact signed decomposition. -/
theorem finiteDimensionalGroundLiftedDefectIntertwiningResidual_eq_zero_of_components
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hTransfer : finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J = 0)
    (hGround : finiteDimensionalGroundProjectorIntertwiningResidualLinearMap Df Dc J = 0) :
    finiteDimensionalGroundLiftedDefectIntertwiningResidualLinearMap Df Dc J = 0 := by
  rw [finiteDimensionalGroundLiftedDefectIntertwiningResidual_decomposition,
    hTransfer, hGround]
  simp

/-- Audit-visible generic cross-carrier compatibility package. -/
structure FiniteDimensionalGroundLiftedDefectCrossCarrierCompatibilityPackage
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) where
  transferResidual : Ec →ₗ[ℝ] Ef
  transferResidual_eq :
    transferResidual = finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J
  groundResidual : Ec →ₗ[ℝ] Ef
  groundResidual_eq :
    groundResidual = finiteDimensionalGroundProjectorIntertwiningResidualLinearMap Df Dc J
  liftedResidual : Ec →ₗ[ℝ] Ef
  liftedResidual_eq :
    liftedResidual = finiteDimensionalGroundLiftedDefectIntertwiningResidualLinearMap Df Dc J
  decomposition : liftedResidual = groundResidual - transferResidual
  componentsSuffice :
    transferResidual = 0 → groundResidual = 0 → liftedResidual = 0

/-- Construct the complete generic cross-carrier compatibility receipt. -/
noncomputable def finiteDimensionalGroundLiftedDefectCrossCarrierCompatibilityPackage
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    FiniteDimensionalGroundLiftedDefectCrossCarrierCompatibilityPackage Df Dc J where
  transferResidual := finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J
  transferResidual_eq := rfl
  groundResidual := finiteDimensionalGroundProjectorIntertwiningResidualLinearMap Df Dc J
  groundResidual_eq := rfl
  liftedResidual := finiteDimensionalGroundLiftedDefectIntertwiningResidualLinearMap Df Dc J
  liftedResidual_eq := rfl
  decomposition := finiteDimensionalGroundLiftedDefectIntertwiningResidual_decomposition Df Dc J
  componentsSuffice :=
    finiteDimensionalGroundLiftedDefectIntertwiningResidual_eq_zero_of_components Df Dc J

end

end MathlibAnalytic
end MGAP4D
