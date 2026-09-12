import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperatorInverse
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The coefficientwise reciprocal of the canonically constructed exact-gap
transfer operator. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperatorInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) : D.StateSpace →L[ℝ] D.StateSpace :=
  orthonormalDiagonalOperator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    (fun i =>
      (Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))⁻¹)

/-- The constructed transfer operator followed by its explicit inverse is the
identity. -/
theorem finite_wilson_constructed_transfer_operator_mul_inverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.transferOperator n * D.transferOperatorInverse n = 1 := by
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperator,
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperatorInverse]
    using
      orthonormalDiagonalOperator_mul_inv
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        (fun i =>
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))
        (fun i => Real.exp_ne_zero _)

/-- The explicit inverse followed by the constructed transfer operator is the
identity. -/
theorem finite_wilson_constructed_transfer_operator_inverse_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.transferOperatorInverse n * D.transferOperator n = 1 := by
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperator,
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperatorInverse]
    using
      orthonormalDiagonalOperator_inv_mul
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        (fun i =>
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))
        (fun i => Real.exp_ne_zero _)

/-- Every canonically constructed finite-volume exact-gap transfer operator is
invertible. -/
theorem finite_wilson_constructed_transfer_operator_isUnit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    IsUnit (D.transferOperator n) := by
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperator]
    using
      orthonormalDiagonalOperator_isUnit
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        (fun i =>
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))
        (fun i => Real.exp_ne_zero _)

/-- On each Hamiltonian eigenmode, the inverse transfer operator acts by
`exp(Eᵢ)`. -/
theorem finite_wilson_constructed_transfer_operator_inverse_on_eigenbasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (i : Fin D.StateDimension) :
    D.transferOperatorInverse n
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) =
      Real.exp ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i) •
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) := by
  rw [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperatorInverse,
    orthonormalDiagonalOperator_apply_basis]
  rw [Real.exp_neg]
  simp

end

end MathlibAnalytic
end MGAP4D
