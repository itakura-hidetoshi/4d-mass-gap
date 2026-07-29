import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputTracking
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelVanishingInputAsymptoticStability

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- The explicit inverse of the constructed finite Wilson Hamiltonian. -/
noncomputable def finiteWilsonConstructedHamiltonianInverseOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) : D.StateSpace →L[ℝ] D.StateSpace :=
  orthonormalDiagonalInverseOperator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)

/-- Constructed finite Wilson left stationary response. -/
noncomputable def finiteWilsonConstructedHamiltonianLeftSteadyState
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) :
    D.StateSpace →L[ℝ] D.StateSpace :=
  finiteWilsonConstructedHamiltonianInverseOperator D n * F_lim

/-- Constructed finite Wilson right stationary response. -/
noncomputable def finiteWilsonConstructedHamiltonianRightSteadyState
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) :
    D.StateSpace →L[ℝ] D.StateSpace :=
  F_lim * finiteWilsonConstructedHamiltonianInverseOperator D n

/-- The constructed Hamiltonian inverse is a right inverse. -/
theorem finite_wilson_constructed_hamiltonian_mul_inverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    LinearMap.toContinuousLinearMap (D.hamiltonian n) *
        finiteWilsonConstructedHamiltonianInverseOperator D n = 1 := by
  simpa [finiteWilsonConstructedHamiltonianInverseOperator,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    orthonormalDiagonalOperator_mul_inverseOperator
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos

/-- The constructed Hamiltonian inverse is also a left inverse. -/
theorem finite_wilson_constructed_inverse_mul_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    finiteWilsonConstructedHamiltonianInverseOperator D n *
        LinearMap.toContinuousLinearMap (D.hamiltonian n) = 1 := by
  simpa [finiteWilsonConstructedHamiltonianInverseOperator,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    orthonormalDiagonalInverseOperator_mul_operator
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos

/-- The constructed left steady state solves the stationary equation. -/
theorem finite_wilson_constructed_hamiltonian_leftSteadyState_stationary
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) :
    LinearMap.toContinuousLinearMap (D.hamiltonian n) *
        finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim = F_lim := by
  rw [finiteWilsonConstructedHamiltonianLeftSteadyState, ← mul_assoc,
    finite_wilson_constructed_hamiltonian_mul_inverse D n, one_mul]

/-- The constructed right steady state solves the stationary equation. -/
theorem finite_wilson_constructed_hamiltonian_rightSteadyState_stationary
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) :
    finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim *
        LinearMap.toContinuousLinearMap (D.hamiltonian n) = F_lim := by
  rw [finiteWilsonConstructedHamiltonianRightSteadyState, mul_assoc,
    finite_wilson_constructed_inverse_mul_hamiltonian D n, mul_one]

/-- The constructed left stationary response is unique. -/
theorem finite_wilson_constructed_hamiltonian_leftSteadyState_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F_lim S : D.StateSpace →L[ℝ] D.StateSpace)
    (hS : LinearMap.toContinuousLinearMap (D.hamiltonian n) * S = F_lim) :
    S = finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim := by
  rw [finiteWilsonConstructedHamiltonianLeftSteadyState]
  calc
    S = finiteWilsonConstructedHamiltonianInverseOperator D n *
        (LinearMap.toContinuousLinearMap (D.hamiltonian n) * S) := by
      rw [← mul_assoc, finite_wilson_constructed_inverse_mul_hamiltonian D n,
        one_mul]
    _ = finiteWilsonConstructedHamiltonianInverseOperator D n * F_lim := by rw [hS]

/-- The constructed right stationary response is unique. -/
theorem finite_wilson_constructed_hamiltonian_rightSteadyState_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F_lim S : D.StateSpace →L[ℝ] D.StateSpace)
    (hS : S * LinearMap.toContinuousLinearMap (D.hamiltonian n) = F_lim) :
    S = finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim := by
  rw [finiteWilsonConstructedHamiltonianRightSteadyState]
  calc
    S = (S * LinearMap.toContinuousLinearMap (D.hamiltonian n)) *
        finiteWilsonConstructedHamiltonianInverseOperator D n := by
      rw [mul_assoc, finite_wilson_constructed_hamiltonian_mul_inverse D n,
        mul_one]
    _ = F_lim * finiteWilsonConstructedHamiltonianInverseOperator D n := by rw [hS]

/-- Constructed finite Wilson left evolution tracks its steady response in norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    Tendsto
      (fun t : ℝ => ‖U t -
        finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖)
      atTop (nhds 0) := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      F U F_lim hF hF_lim hUdiag

/-- Constructed finite Wilson right evolution tracks its steady response in norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    Tendsto
      (fun t : ℝ => ‖U t -
        finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖)
      atTop (nhds 0) := by
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
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      F U F_lim hF hF_lim hUdiag

/-- Constructed left evolution converges in operator space to the steady state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_leftSteadyState_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    Tendsto U atTop
      (nhds (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim)) :=
  tendsto_of_tendsto_norm_sub_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      D n F U F_lim hF hF_lim hU)

/-- Constructed right evolution converges in operator space to the steady state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_rightSteadyState_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    Tendsto U atTop
      (nhds (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim)) :=
  tendsto_of_tendsto_norm_sub_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      D n F U F_lim hF hF_lim hU)

/-- Constructed left tracking holds strongly on every fixed state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (x : D.StateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim x)) :=
  continuousLinearMap_tendsto_apply_of_tendsto_norm_sub_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      D n F U F_lim hF hF_lim hU) x

/-- Constructed right tracking holds strongly on every fixed state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (x : D.StateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim x)) :=
  continuousLinearMap_tendsto_apply_of_tendsto_norm_sub_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      D n F U F_lim hF hF_lim hU) x

/-- Constructed left tracking is uniform on the closed unit ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : D.StateSpace, ‖x‖ ≤ 1 →
        ‖U t x - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim x‖ < ε :=
  continuousLinearMap_eventually_uniform_unitBall_of_tendsto_norm_sub_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      D n F U F_lim hF hF_lim hU)

/-- Constructed right tracking is uniform on the closed unit ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : D.StateSpace, ‖x‖ ≤ 1 →
        ‖U t x - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim x‖ < ε :=
  continuousLinearMap_eventually_uniform_unitBall_of_tendsto_norm_sub_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      D n F U F_lim hF hF_lim hU)

end

end MathlibAnalytic
end MGAP4D
