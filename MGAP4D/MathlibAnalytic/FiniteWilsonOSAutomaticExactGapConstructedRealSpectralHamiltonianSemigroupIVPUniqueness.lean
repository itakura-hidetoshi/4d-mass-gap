import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The constructed finite Wilson real spectral semigroup is the unique
operator-norm solution of `U' = -H U`, `U 0 = 1`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_eq_of_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U 0 = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U t) t) :
    U = D.realSpectralHamiltonianSemigroup n := by
  have hUdiag : ∀ t : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U t) t := by
    intro t
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU t
  have h := orthonormalDiagonalHamiltonianSemigroup_eq_of_hasDerivAt_operator_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    U hU0 hUdiag
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup]
    using h

end

end MathlibAnalytic
end MGAP4D
