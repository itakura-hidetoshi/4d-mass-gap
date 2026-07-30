import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorBoundedInputDifferencePairwiseInputToStateBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputMatrixElementUniformHalfMinSimplifiedBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

section Left

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ) (t₀ : ℝ)
variable (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
variable (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U ((-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V ((-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) * V r + G r) r)

include n F G hC hF hG hFG hU0 hV0 hU hV

/-- On `Ω⊥`, left trajectories with uniformly bounded input mismatch satisfy
    the exact-gap input-to-state estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_left
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV

/-- On `Ω⊥`, left operator distance enters every positive neighborhood of the
    exact input floor. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_left
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ C / exactGapValueReal + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, left input-to-state control acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_left
    (t : ℝ) (ht : t₀ ≤ t) (y : D.gapData.ExcitedStateSpace) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV

/-- On `Ω⊥`, left matrix elements inherit the input-to-state envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_left
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, direct left matrix-element differences satisfy the same envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_left
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, fixed left matrix elements enter every positive neighborhood of
    their exact input floor. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
    (x y : D.gapData.ExcitedStateSpace) (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) /
            exactGapValueReal) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
          (C / exactGapValueReal) * ‖x‖ * ‖y‖ + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, one full-gap waiting time controls every left matrix element on
    both closed unit balls up to the exact input floor. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
            C / exactGapValueReal + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ) (t₀ : ℝ)
variable (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
variable (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) + G r) r)

include n F G hC hF hG hFG hU0 hV0 hU hV

/-- On `Ω⊥`, right trajectories with uniformly bounded input mismatch satisfy
    the exact-gap input-to-state estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_right
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_inputToState_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV

/-- On `Ω⊥`, right operator distance enters every positive neighborhood of the
    exact input floor. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_right
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ C / exactGapValueReal + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_norm_sub_le_floor_add_epsilon_after_inputToState_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, right input-to-state control acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_right
    (t : ℝ) (ht : t₀ ≤ t) (y : D.gapData.ExcitedStateSpace) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_pointwise_inputToState_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV

/-- On `Ω⊥`, right matrix elements inherit the input-to-state envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_right
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_inputToState_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, direct right matrix-element differences satisfy the same envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_right
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        C / exactGapValueReal) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_inputToState_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, fixed right matrix elements enter every positive neighborhood of
    their exact input floor. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
    (x y : D.gapData.ExcitedStateSpace) (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) /
            exactGapValueReal) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
          (C / exactGapValueReal) * ‖x‖ * ‖y‖ + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, one full-gap waiting time controls every right matrix element on
    both closed unit balls up to the exact input floor. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
            C / exactGapValueReal + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_unitBall_matrixElement_sub_le_floor_add_epsilon_after_inputToState_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

end Right

end

end MathlibAnalytic
end MGAP4D
