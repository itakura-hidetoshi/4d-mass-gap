import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformSubcritical
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeTunableResonant

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left tracking at every rate below both the exact gap
and the forcing-tail rate, uniformly across resonance. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ ν : ℝ) (hνpos : 0 < ν)
    (hνgap : ν < exactGapValueReal) (hνμ : ν < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
          C / (max exactGapValueReal μ - ν)) *
        Real.exp (-((t - t₀) * ν)) := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ ν (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hνpos hνgap hνμ t₀ t ht A F U F_lim C hC hF hFC hU0 hUdiag

/-- Constructed finite Wilson right tracking has the same uniform subcritical
envelope and requires no commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ ν : ℝ) (hνpos : 0 < ν)
    (hνgap : ν < exactGapValueReal) (hνμ : ν < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
          C / (max exactGapValueReal μ - ν)) *
        Real.exp (-((t - t₀) * ν)) := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ ν (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hνpos hνgap hνμ t₀ t ht A F U F_lim C hC hF hFC hU0 hUdiag

end

end MathlibAnalytic
end MGAP4D
