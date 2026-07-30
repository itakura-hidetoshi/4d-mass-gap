import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorVanishingInputDifferencePairwiseAsymptoticIncrementalStabilityBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorInputProfilePairwiseConvolutionSharpFiniteHorizonBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

private theorem finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
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

private theorem finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
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

section Left

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
variable (n : ℕ)
variable (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFG0 : Tendsto (fun t : ℝ => ‖F t - G t‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U
    ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V
    ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)

include n F G hF hG hFG0 hU hV

/-- Constructed finite Wilson left trajectories become asymptotically
indistinguishable whenever their input mismatch vanishes in norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left :
    Tendsto (fun t : ℝ => ‖U t - V t‖) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n G V hV)

/-- The constructed left operator difference converges to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_left :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n G V hV)

/-- The constructed left operator difference converges strongly on each state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_left
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n G V hV) y

/-- Direct constructed left action differences converge to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_left
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n G V hV) y

/-- Every fixed constructed left matrix-element difference converges to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_left
    (x y : D.StateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n G V hV) x y

/-- Absolute constructed left matrix-element differences converge to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_left
    (x y : D.StateSpace) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n G V hV) x y

/-- One eventual time controls all constructed left matrix elements on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_left :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| < ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_left_deriv_diagonal
        D n G V hV)

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
variable (n : ℕ)
variable (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFG0 : Tendsto (fun t : ℝ => ‖F t - G t‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U
    (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V
    (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)

include n F G hF hG hFG0 hU hV

/-- Constructed finite Wilson right trajectories have the same asymptotic
incremental stability without a commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right :
    Tendsto (fun t : ℝ => ‖U t - V t‖) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n G V hV)

/-- The constructed right operator difference converges to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_right :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n G V hV)

/-- The constructed right operator difference converges strongly on each state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_right
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n G V hV) y

/-- Direct constructed right action differences converge to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_right
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n G V hV) y

/-- Every fixed constructed right matrix-element difference converges to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_right
    (x y : D.StateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n G V hV) x y

/-- Absolute constructed right matrix-element differences converge to zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_right
    (x y : D.StateSpace) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n G V hV) x y

/-- One eventual time controls all constructed right matrix elements on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_right :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| < ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos F G U V hF hG hFG0
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n F U hU)
      (finite_wilson_constructed_vanishingInputDifference_right_deriv_diagonal
        D n G V hV)

end Right

end

end MathlibAnalytic
end MGAP4D
