import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorCommonInputPairwiseFullGapBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private theorem finiteWilsonConstructed_commonInput_left_deriv_diagonal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ∀ r, HasDerivAt U
      ((-orthonormalDiagonalOperator
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
  intro r
  simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r

private theorem finiteWilsonConstructed_commonInput_right_deriv_diagonal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ∀ r, HasDerivAt U
      (U r * (-orthonormalDiagonalOperator
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
  intro r
  simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r

/-- Constructed finite Wilson left common-input contraction at the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F V hV)

/-- Constructed finite Wilson right common-input contraction at the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r, HasDerivAt V
      (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F V hV)

/-- Constructed finite Wilson left operator-distance settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ) (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
      ‖U t - V t‖ ≤ ε := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F V hV) ε hε

/-- Constructed finite Wilson right operator-distance settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ) (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r, HasDerivAt V
      (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
      ‖U t - V t‖ ≤ ε := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F V hV) ε hε

/-- Constructed finite Wilson left pointwise pairwise contraction. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F y hU0 hV0
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F V hV)

/-- Constructed finite Wilson right pointwise pairwise contraction. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r, HasDerivAt V
      (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F y hU0 hV0
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F V hV)

/-- Constructed finite Wilson left matrix-element contraction. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F x y hU0 hV0
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F V hV)

/-- Constructed finite Wilson right matrix-element contraction. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r, HasDerivAt V
      (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F x y hU0 hV0
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F V hV)

/-- Constructed finite Wilson left matrix-element settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ) (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0
      (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
      |inner ℝ x ((U t - V t) y)| ≤ ε := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ A B U V F x y hU0 hV0
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F V hV) ε hε

/-- Constructed finite Wilson right matrix-element settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ) (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r, HasDerivAt V
      (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0
      (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
      |inner ℝ x ((U t - V t) y)| ≤ ε := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ A B U V F x y hU0 hV0
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F V hV) ε hε

/-- Constructed finite Wilson left unit-ball matrix-element settling. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ) (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
      ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F V hV) ε hε

/-- Constructed finite Wilson right unit-ball matrix-element settling. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ) (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r, HasDerivAt V
      (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t, t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
      ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F V hV) ε hε

/-- Constructed finite Wilson left forward uniqueness under arbitrary common input. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r, HasDerivAt V
      ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (hAB : A = B) : U t = V t := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_left
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_left_deriv_diagonal D n F V hV) hAB

/-- Constructed finite Wilson right forward uniqueness under arbitrary common input. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r, HasDerivAt U
      (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r, HasDerivAt V
      (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hAB : A = B) : U t = V t := by
  exact orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_right
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
    t₀ t ht A B U V F hU0 hV0
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F U hU)
    (finiteWilsonConstructed_commonInput_right_deriv_diagonal D n F V hV) hAB

end

end MathlibAnalytic
end MGAP4D
