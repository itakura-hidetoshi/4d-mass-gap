import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasFiniteHorizonBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

private theorem finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal
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

private theorem finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal
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
variable (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
variable (A B Qinf : D.StateSpace →L[ℝ] D.StateSpace)
variable (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)

include n ht hF hG hU0 hV0 hU hV

/-- Constructed finite Wilson left affine error retains the complete residual profile. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left :
    ‖(U t - V t) -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV)

/-- Constructed left affine finite-horizon control acts on every state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_left
    (y : D.StateSpace) :
    ‖U t y - V t y -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV) y

/-- Constructed left matrix-element errors retain the complete residual profile. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_left
    (x y : D.StateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV) x y

/-- One constructed left profile bound controls both closed unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_left :
    ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
            ‖(F s - G s) - Qinf‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV)

/-- Constructed left affine error has the sharp gain under a bounded residual. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ‖(U t - V t) -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV)
      C hC hFG

/-- Constructed sharp left residual control acts on every state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (y : D.StateSpace) :
    ‖U t y - V t y -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV)
      C hC hFG y

/-- Constructed sharp left residual control for every matrix element. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (x y : D.StateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV)
      C hC hFG x y

/-- One sharp constructed left residual bound controls both closed unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
          ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv_diagonal D n G V hV)
      C hC hFG

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
variable (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
variable (A B Qinf : D.StateSpace →L[ℝ] D.StateSpace)
variable (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)

include n ht hF hG hU0 hV0 hU hV

/-- Constructed right affine error retains the complete residual profile without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right :
    ‖(U t - V t) -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV)

/-- Constructed right affine finite-horizon control acts on every state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_right
    (y : D.StateSpace) :
    ‖U t y - V t y -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV) y

/-- Constructed right matrix-element errors retain the complete residual profile. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_right
    (x y : D.StateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV) x y

/-- One constructed right profile bound controls both closed unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_right :
    ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
            ‖(F s - G s) - Qinf‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV)

/-- Constructed right affine error has the sharp residual gain without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ‖(U t - V t) -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV)
      C hC hFG

/-- Constructed sharp right residual control acts on every state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (y : D.StateSpace) :
    ‖U t y - V t y -
        finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV)
      C hC hFG y

/-- Constructed sharp right residual control for every matrix element. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (x y : D.StateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV)
      C hC hFG x y

/-- One sharp constructed right residual bound controls both closed unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
          ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B Qinf F G U V hF hG hU0 hV0
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv_diagonal D n G V hV)
      C hC hFG

end Right

end

end MathlibAnalytic
end MGAP4D
