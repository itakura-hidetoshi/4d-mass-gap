import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorExp
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupEvolution
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralScalarExtension

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The eigenbasis diagonal operator is the original constructed Hamiltonian as
a continuous real-linear operator. -/
theorem finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    orthonormalDiagonalOperator
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) =
      LinearMap.toContinuousLinearMap (D.hamiltonian n) := by
  have hdiag := symmetric_eq_orthonormalDiagonalLinearMap
    (D.hamiltonian n) (D.hamiltonianSymmetric n) D.stateFinrank
  unfold orthonormalDiagonalOperator
  exact congrArg LinearMap.toContinuousLinearMap hdiag.symm

/-- Ordinary operator-norm derivative form of the constructed left evolution
equation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_deriv_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    deriv (D.realSpectralHamiltonianSemigroup n) t =
      (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) *
        D.realSpectralHamiltonianSemigroup n t :=
  (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_left
    D n t).deriv

/-- Ordinary operator-norm derivative form of the constructed right evolution
equation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_deriv_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    deriv (D.realSpectralHamiltonianSemigroup n) t =
      D.realSpectralHamiltonianSemigroup n t *
        (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) :=
  (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_operator_right
    D n t).deriv

/-- The original constructed Hamiltonian commutes with every real spectral time
slice. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_commutes_hamiltonian_explicit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    LinearMap.toContinuousLinearMap (D.hamiltonian n) *
        D.realSpectralHamiltonianSemigroup n t =
      D.realSpectralHamiltonianSemigroup n t *
        LinearMap.toContinuousLinearMap (D.hamiltonian n) := by
  have h := orthonormalDiagonalHamiltonianSemigroup_commutes_hamiltonian_explicit
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) t
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup,
    orthonormalDiagonalHamiltonianSemigroup,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
    using h

/-- The constructed real spectral semigroup is exactly the operator exponential
of the negative time-scaled original Hamiltonian. -/
theorem finite_wilson_constructed_normedSpace_exp_neg_hamiltonian_eq_real_spectralSemigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    NormedSpace.exp
        (-(t • LinearMap.toContinuousLinearMap (D.hamiltonian n))) =
      D.realSpectralHamiltonianSemigroup n t := by
  have h := normedSpace_exp_neg_smul_orthonormalDiagonalOperator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) t
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup,
    orthonormalDiagonalHamiltonianSemigroup,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
    using h

/-- Literal complex scalar extension intertwines the real operator exponential
with the established complex spectral semigroup at every time. -/
theorem finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_real_operatorExp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    (D.complexSpectralScalarExtensionEquiv n).toLinearMap.comp
        ((NormedSpace.exp
          (-(t • LinearMap.toContinuousLinearMap (D.hamiltonian n)))).toLinearMap.baseChange ℂ) =
      (D.complexSpectralHamiltonianSemigroup n t).toLinearMap.comp
        (D.complexSpectralScalarExtensionEquiv n).toLinearMap := by
  rw [finite_wilson_constructed_normedSpace_exp_neg_hamiltonian_eq_real_spectralSemigroup
    D n t]
  exact finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_semigroup
    D n t

end

end MathlibAnalytic
end MGAP4D
