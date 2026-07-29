import MGAP4D.MathlibAnalytic.OrthonormalComplexScalarExtension
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperatorInverse
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroupGenerator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped TensorProduct

/-- The literal extension of scalars of the constructed real finite-dimensional
state space. -/
abbrev
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexScalarExtensionStateSpace
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W) :
    Type :=
  ℂ ⊗[ℝ] D.StateSpace

/-- The complex spectral realization is literally the scalar extension of the
constructed real state space, with `1 ⊗ eᵢ` identified with complex mode `i`. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralScalarExtensionEquiv
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexScalarExtensionStateSpace ≃ₗ[ℂ] D.complexSpectralStateSpace :=
  orthonormalComplexScalarExtensionEquiv
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    D.complexSpectralBasis

/-- The constructed scalar-extension equivalence matches the real and complex
Hamiltonian mode bases. -/
@[simp]
theorem finite_wilson_constructed_complex_spectral_scalarExtensionEquiv_one_tmul_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (i : Fin D.StateDimension) :
    D.complexSpectralScalarExtensionEquiv n
        (1 ⊗ₜ[ℝ]
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i)) =
      D.complexSpectralBasis i := by
  exact orthonormalComplexScalarExtensionEquiv_one_tmul_basis
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    D.complexSpectralBasis i

/-- The real continuous-time spectral semigroup before extension of scalars. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    D.StateSpace →L[ℝ] D.StateSpace :=
  orthonormalDiagonalOperator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    (fun i => Real.exp (-(t *
      (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))

/-- Time zero is the identity on the real spectral realization. -/
@[simp]
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.realSpectralHamiltonianSemigroup n 0 = 1 := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup
  convert orthonormalDiagonalOperator_one
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank) using 1
  funext i
  simp

/-- The real spectral time slices satisfy the semigroup law. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_add
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (s t : ℝ) :
    D.realSpectralHamiltonianSemigroup n (s + t) =
      D.realSpectralHamiltonianSemigroup n s *
        D.realSpectralHamiltonianSemigroup n t := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup
  rw [orthonormalDiagonalOperator_mul]
  congr 1
  funext i
  rw [← Real.exp_add]
  congr 1
  ring

/-- Time one recovers the real constructed transfer operator. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.realSpectralHamiltonianSemigroup n 1 = D.transferOperator n := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperator
  congr 1
  funext i
  simp

/-- The real spectral semigroup acts modewise by `exp (-tEᵢ)`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (i : Fin D.StateDimension) :
    D.realSpectralHamiltonianSemigroup n t
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) =
      Real.exp (-(t *
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)) •
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup
  exact orthonormalDiagonalOperator_apply_basis _ _ i

/-- The scalar-extension equivalence intertwines the real constructed transfer
operator with the complex spectral transfer operator. -/
theorem finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_transfer
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    (D.complexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.transferOperator n).toLinearMap.baseChange ℂ) =
      (D.complexSpectralTransferOperator n).toLinearMap.comp
        (D.complexSpectralScalarExtensionEquiv n).toLinearMap := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralScalarExtensionEquiv
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperator
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator
  exact orthonormalComplexScalarExtensionEquiv_intertwines_diagonalOperator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    D.complexSpectralBasis
    (fun i => Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))

/-- The scalar-extension equivalence identifies the original real Hamiltonian
with the explicit complex spectral Hamiltonian. -/
theorem finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    (D.complexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.hamiltonian n).baseChange ℂ) =
      (D.complexSpectralHamiltonian n).toLinearMap.comp
        (D.complexSpectralScalarExtensionEquiv n).toLinearMap := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralScalarExtensionEquiv
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonian
  simpa [orthonormalComplexDiagonalOperator]
    using orthonormalComplexScalarExtensionEquiv_intertwines_symmetric
      (D.hamiltonian n) (D.hamiltonianSymmetric n) D.stateFinrank
      D.complexSpectralBasis

/-- The same scalar-extension equivalence identifies the original real
Hamiltonian with the canonical complex logarithmic Hamiltonian. -/
theorem finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    (D.complexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.hamiltonian n).baseChange ℂ) =
      (D.complexSpectralLogHamiltonian n).toLinearMap.comp
        (D.complexSpectralScalarExtensionEquiv n).toLinearMap := by
  rw [finite_wilson_constructed_complex_spectral_logHamiltonian_eq_hamiltonian D n]
  exact finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_hamiltonian
    D n

/-- Extension of scalars intertwines every real spectral time slice with the
complex continuous-time Hamiltonian semigroup. -/
theorem finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_semigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    (D.complexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((D.realSpectralHamiltonianSemigroup n t).toLinearMap.baseChange ℂ) =
      (D.complexSpectralHamiltonianSemigroup n t).toLinearMap.comp
        (D.complexSpectralScalarExtensionEquiv n).toLinearMap := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralScalarExtensionEquiv
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexScalarExtensionEquiv_intertwines_diagonalOperator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    D.complexSpectralBasis
    (fun i => Real.exp (-(t *
      (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))

end

end MathlibAnalytic
end MGAP4D
