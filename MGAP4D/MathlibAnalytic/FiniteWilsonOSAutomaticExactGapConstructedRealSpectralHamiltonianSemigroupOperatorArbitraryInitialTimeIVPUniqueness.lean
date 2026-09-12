import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorArbitraryInitialTimeIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The constructed finite Wilson real spectral semigroup, based at an arbitrary
initial time `t₀`, is the unique operator-norm solution of `U' = -H U` with
`U t₀ = 1`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U t) t) :
    U = fun t : ℝ => D.realSpectralHamiltonianSemigroup n (t - t₀) := by
  have hUdiag : ∀ t : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U t) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU t
  have h := orthonormalDiagonalHamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ U hU0 hUdiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

/-- The constructed finite Wilson real spectral semigroup, based at an arbitrary
initial time `t₀`, is the unique operator-norm solution of `U' = U (-H)` with
`U t₀ = 1`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-LinearMap.toContinuousLinearMap (D.hamiltonian n))) t) :
    U = fun t : ℝ => D.realSpectralHamiltonianSemigroup n (t - t₀) := by
  have hUdiag : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank))) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU t
  have h := orthonormalDiagonalHamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    t₀ U hU0 hUdiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

end

end MathlibAnalytic
end MGAP4D
