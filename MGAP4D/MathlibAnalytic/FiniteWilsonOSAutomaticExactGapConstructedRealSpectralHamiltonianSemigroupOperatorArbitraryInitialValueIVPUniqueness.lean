import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorArbitraryInitialValueIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For arbitrary initial operator `A` at time `t₀`, the constructed finite Wilson
left Hamiltonian IVP has solution `S (t - t₀) A`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_sub_mul_eq_of_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U t) t) :
    U = fun t : ℝ => D.realSpectralHamiltonianSemigroup n (t - t₀) * A := by
  have hUdiag : ∀ t : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U t) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU t
  have h := orthonormalDiagonalHamiltonianSemigroup_sub_mul_eq_of_hasDerivAt_operator_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ A U hU0 hUdiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

/-- For arbitrary initial operator `A` at time `t₀`, the constructed finite Wilson
right Hamiltonian IVP has solution `A S (t - t₀)`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_mul_sub_eq_of_hasDerivAt_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-LinearMap.toContinuousLinearMap (D.hamiltonian n))) t) :
    U = fun t : ℝ => A * D.realSpectralHamiltonianSemigroup n (t - t₀) := by
  have hUdiag : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank))) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU t
  have h := orthonormalDiagonalHamiltonianSemigroup_mul_sub_eq_of_hasDerivAt_operator_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ A U hU0 hUdiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

end

end MathlibAnalytic
end MGAP4D
