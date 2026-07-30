import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputMatrixElementUniformHalfMinSimplifiedBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplifiedSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left pointwise tracking at the exact-gap half-min rate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖(U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y‖ ≤
      ((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ t ht A F U F_lim C hC hF hFC y hU0 hUdiag

/-- Constructed finite Wilson right pointwise tracking at the same rate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖(U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y‖ ≤
      ((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ t ht A F U F_lim C hC hF hFC y hU0 hUdiag

/-- Constructed finite Wilson left matrix-element tracking at the exact-gap half-min rate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    |inner ℝ x ((U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y)| ≤
      ((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ t ht A F U F_lim C hC hF hFC x y hU0 hUdiag

/-- Constructed finite Wilson right matrix-element tracking at the same rate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    |inner ℝ x ((U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y)| ≤
      ((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ t ht A F U F_lim C hC hF hFC x y hU0 hUdiag

/-- Constructed finite Wilson left matrix-element tracking reaches every tolerance
    after the explicit exact-gap half-min waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y)| ≤ ε := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hUdiag ε hε

/-- Constructed finite Wilson right matrix-element tracking has the identical settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y)| ≤ ε := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hUdiag ε hε

/-- Constructed finite Wilson left matrix elements converge directly to the steady
    matrix element after the explicit vector-dependent waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim y)| ≤ ε := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hUdiag ε hε

/-- Constructed finite Wilson right matrix elements have the identical direct settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim y)| ≤ ε := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hUdiag ε hε

/-- Constructed finite Wilson left matrix elements settle uniformly over both closed
    unit balls after the operator-norm half-min waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) / ε) /
              (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim y)| ≤ ε := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianLeftSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_leftSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ A F U F_lim C hC hF hFC hU0 hUdiag ε hε

/-- Constructed finite Wilson right matrix elements have the identical uniform unit-ball settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) / ε) /
              (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim y)| ≤ ε := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  simpa [finiteWilsonConstructedHamiltonianRightSteadyState,
    finiteWilsonConstructedHamiltonianInverseOperator,
    orthonormalDiagonalHamiltonian_rightSteadyState] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ A F U F_lim C hC hF hFC hU0 hUdiag ε hε

end

end MathlibAnalytic
end MGAP4D
