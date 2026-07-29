import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputPracticalTrackingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputTracking

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left evolution satisfies the exact finite-time
tracking gain relative to its stationary response. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) /
          exactGapValueReal) * M := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U F_lim M hF hFM hU0 hUdiag

/-- Constructed finite Wilson right evolution has the same exact tracking gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) /
          exactGapValueReal) * M := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_gain_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U F_lim M hF hFM hU0 hUdiag

/-- Constructed finite Wilson left tracking is bounded by a decaying mismatch
plus the exact-gap static tail gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
        M / exactGapValueReal := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U F_lim M hM hF hFM hU0 hUdiag

/-- Constructed finite Wilson right tracking has the identical static tail gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
        M / exactGapValueReal := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tracking_ultimate_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A F U F_lim M hM hF hFM hU0 hUdiag

/-- Constructed finite Wilson left evolution enters the explicit exact-gap
tracking tube after the logarithmic settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ / ε) /
              exactGapValueReal) ≤ t →
        ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤
          M / exactGapValueReal + ε := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A F U F_lim M hM hF hFM hU0 hUdiag ε hε

/-- Constructed finite Wilson right evolution has the same practical tracking tube. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s - F_lim‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ / ε) /
              exactGapValueReal) ≤ t →
        ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤
          M / exactGapValueReal + ε := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_trackingTube_after_settlingTime_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A F U F_lim M hM hF hFM hU0 hUdiag ε hε

/-- A half-budget tail bound gives an explicit full `ε` tracking time for the
constructed left evolution. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_tail_settlingTime_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (ε : ℝ)
    (hε : 0 < ε)
    (hFtail : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ exactGapValueReal * (ε / 2))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ /
              (ε / 2)) / exactGapValueReal) ≤ t →
        ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤ ε := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_tail_settlingTime_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A F U F_lim hF ε hε hFtail hU0 hUdiag

/-- The identical half-budget tail condition yields the right tracking time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_tail_settlingTime_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (ε : ℝ)
    (hε : 0 < ε)
    (hFtail : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ exactGapValueReal * (ε / 2))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ /
              (ε / 2)) / exactGapValueReal) ≤ t →
        ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤ ε := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_tail_settlingTime_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A F U F_lim hF ε hε hFtail hU0 hUdiag

end

end MathlibAnalytic
end MGAP4D
