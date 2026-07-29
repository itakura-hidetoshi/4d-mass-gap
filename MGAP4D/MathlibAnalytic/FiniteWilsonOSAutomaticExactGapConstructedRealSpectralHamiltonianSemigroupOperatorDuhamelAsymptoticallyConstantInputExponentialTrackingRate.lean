import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingRate
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputTracking

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson non-resonant closed-form tracking rate for left
Hamiltonian multiplication. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (μ : ℝ)
    (hgapμ : exactGapValueReal ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (C : ℝ)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
        ((Real.exp (-((t - t₀) * μ)) -
            Real.exp (-((t - t₀) * exactGapValueReal))) /
          (exactGapValueReal - μ)) * C := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hgapμ t₀ t ht A F U F_lim C hF hFC hU0 hUdiag

/-- Constructed finite Wilson non-resonant closed-form tracking rate for right
Hamiltonian multiplication. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (μ : ℝ)
    (hgapμ : exactGapValueReal ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (C : ℝ)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
        ((Real.exp (-((t - t₀) * μ)) -
            Real.exp (-((t - t₀) * exactGapValueReal))) /
          (exactGapValueReal - μ)) * C := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hgapμ t₀ t ht A F U F_lim C hF hFC hU0 hUdiag

/-- Constructed finite Wilson resonant closed-form tracking rate for left
Hamiltonian multiplication. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (C : ℝ)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤
        C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
        ((t - t₀) * Real.exp (-((t - t₀) * exactGapValueReal))) * C := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A F U F_lim C hF hFC hU0 hUdiag

/-- Constructed finite Wilson resonant closed-form tracking rate for right
Hamiltonian multiplication. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (C : ℝ)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤
        C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
        ((t - t₀) * Real.exp (-((t - t₀) * exactGapValueReal))) * C := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A F U F_lim C hF hFC hU0 hUdiag

end

end MathlibAnalytic
end MGAP4D
