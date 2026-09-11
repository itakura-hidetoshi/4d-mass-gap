import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorBoundedInputDifferencePairwiseInputToStateBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputMatrixElementUniformHalfMinSimplifiedBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private theorem finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
  intro r
  simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r

private theorem finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
  intro r
  simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r

/-- Constructed finite Wilson left trajectories with uniformly bounded input
    mismatch satisfy the exact-gap input-to-state estimate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right trajectories with uniformly bounded input
    mismatch satisfy the exact-gap input-to-state estimate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson left operator distance enters every positive
    neighborhood of the exact input floor. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ C / exactGapValueReal + ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n G V hV)
      ε hε

/-- Constructed finite Wilson right operator distance enters every positive
    neighborhood of the exact input floor. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ C / exactGapValueReal + ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n G V hV)
      ε hε

/-- Constructed finite Wilson left input-to-state control acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right input-to-state control acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson left matrix elements inherit the input-to-state envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right matrix elements inherit the input-to-state envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson direct left matrix-element differences satisfy the same envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson direct right matrix-element differences satisfy the same envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson fixed left matrix elements enter every positive
    neighborhood of their exact input floor. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) /
            exactGapValueReal) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
          (C / exactGapValueReal) * ‖x‖ * ‖y‖ + ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A B F G U V C hC hF hG hFG x y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n G V hV)
      ε hε

/-- Constructed finite Wilson fixed right matrix elements enter every positive
    neighborhood of their exact input floor. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) /
            exactGapValueReal) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
          (C / exactGapValueReal) * ‖x‖ * ‖y‖ + ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A B F G U V C hC hF hG hFG x y hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n G V hV)
      ε hε

/-- Constructed finite Wilson left matrix elements are uniformly controlled on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
            C / exactGapValueReal + ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_left_deriv_diagonal D n G V hV)
      ε hε

/-- Constructed finite Wilson right matrix elements are uniformly controlled on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
            C / exactGapValueReal + ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      t₀ A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_boundedInputDifference_right_deriv_diagonal D n G V hV)
      ε hε

end

end MathlibAnalytic
end MGAP4D
