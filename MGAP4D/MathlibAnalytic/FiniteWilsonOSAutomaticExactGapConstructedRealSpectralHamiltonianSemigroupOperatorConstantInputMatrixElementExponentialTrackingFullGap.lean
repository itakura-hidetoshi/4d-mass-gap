import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputPointwiseExponentialTrackingFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left tracking has full exact-gap decay in every
    matrix element under exactly constant input. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r) :
    |inner ℝ x
      ((U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y)| ≤
      (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ *
        Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F_lim) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A U F_lim x y hU0 hUdiag

/-- Constructed finite Wilson right tracking has the identical matrix-element
    estimate and requires no commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r) :
    |inner ℝ x
      ((U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y)| ≤
      (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ *
        Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F_lim) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A U F_lim x y hU0 hUdiag

end

end MathlibAnalytic
end MGAP4D
