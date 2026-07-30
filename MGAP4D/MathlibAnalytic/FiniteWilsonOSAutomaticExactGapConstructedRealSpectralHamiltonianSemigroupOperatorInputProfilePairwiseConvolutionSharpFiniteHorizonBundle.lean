import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorInputProfilePairwiseConvolutionSharpFiniteHorizonBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorBoundedInputDifferencePairwiseInputToStateBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

private theorem finite_wilson_constructed_inputProfile_left_deriv_diagonal
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

private theorem finite_wilson_constructed_inputProfile_right_deriv_diagonal
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

/-- Constructed finite Wilson left trajectories retain the complete input-difference convolution. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG hU0 hV0
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right trajectories retain the complete convolution. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG hU0 hV0
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson left convolution control acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G) (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG y hU0 hV0
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right convolution control acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G) (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG y hU0 hV0
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson left matrix elements retain the complete convolution. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG x y hU0 hV0
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right matrix elements retain the complete convolution. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG x y hU0 hV0
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n G V hV)

/-- Direct constructed finite Wilson left matrix-element differences retain the convolution. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG x y hU0 hV0
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n G V hV)

/-- Direct constructed finite Wilson right matrix-element differences retain the convolution. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG x y hU0 hV0
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson left convolution control is uniform on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG hU0 hV0
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right convolution control is uniform on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      t₀ t ht A B F G U V hF hG hU0 hV0
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson left trajectories have the sharp finite-horizon bounded-input gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_left
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
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n G V hV)

/-- Constructed finite Wilson right trajectories have the sharp finite-horizon gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_right
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
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
      t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n G V hV)

/-- Equal initial constructed finite Wilson left trajectories have pure input gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ‖U t - V t‖ ≤
      ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
      t₀ t ht A F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_left_deriv_diagonal D n G V hV)

/-- Equal initial constructed finite Wilson right trajectories have pure input gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ‖U t - V t‖ ≤
      ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) exactGapValueReal_pos
      t₀ t ht A F G U V C hC hF hG hFG hU0 hV0
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_inputProfile_right_deriv_diagonal D n G V hV)

end

end MathlibAnalytic
end MGAP4D