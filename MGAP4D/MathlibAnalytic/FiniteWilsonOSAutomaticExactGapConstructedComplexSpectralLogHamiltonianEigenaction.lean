import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralLogHamiltonian
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorExpLog

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit complex spectral Hamiltonian with the same eigenvalue list as
the constructed real finite-dimensional Hamiltonian. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace :=
  orthonormalComplexDiagonalOperator D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)

/-- Every constructed Hamiltonian mode coefficient is nonnegative. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonian_eigenvalue_nonneg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.StateDimension) :
    0 ≤ (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i :=
  exactGapValueReal_pos.le.trans (D.hamiltonianEigenvalues_ge_exactGap n i)

/-- The explicit complex spectral Hamiltonian is positive. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonian_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    (D.complexSpectralHamiltonian n).IsPositive := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonian
  apply orthonormalComplexDiagonalOperator_isPositive
  exact finite_wilson_constructed_complex_spectral_hamiltonian_eigenvalue_nonneg D n

/-- Exponentiating the negative explicit complex spectral Hamiltonian recovers
the constructed complex spectral transfer operator. -/
theorem finite_wilson_constructed_complex_spectral_exp_neg_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    NormedSpace.exp (-D.complexSpectralHamiltonian n) =
      D.complexSpectralTransferOperator n := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonian
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator
  exact normedSpace_exp_neg_orthonormalComplexDiagonalOperator
    D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)

/-- The canonical CFC logarithmic Hamiltonian is exactly the explicit complex
spectral Hamiltonian with the original finite-volume energy eigenvalues. -/
theorem finite_wilson_constructed_complex_spectral_logHamiltonian_eq_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralLogHamiltonian n = D.complexSpectralHamiltonian n := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralLogHamiltonian
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonian
  exact complexStrictlyPositive_logHamiltonian_exp_neg_diagonal_eq
    D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)
    (finite_wilson_constructed_complex_spectral_hamiltonian_eigenvalue_nonneg D n)

/-- The recovered logarithmic Hamiltonian acts on mode `i` by the original
Hamiltonian eigenvalue `Eᵢ`. -/
theorem finite_wilson_constructed_complex_spectral_logHamiltonian_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.StateDimension) :
    D.complexSpectralLogHamiltonian n (D.complexSpectralBasis i) =
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i : ℂ) •
        D.complexSpectralBasis i := by
  rw [finite_wilson_constructed_complex_spectral_logHamiltonian_eq_hamiltonian D n]
  exact orthonormalComplexDiagonalOperator_apply_basis
    D.complexSpectralBasis
    (fun j => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank j) i

end

end MathlibAnalytic
end MGAP4D
