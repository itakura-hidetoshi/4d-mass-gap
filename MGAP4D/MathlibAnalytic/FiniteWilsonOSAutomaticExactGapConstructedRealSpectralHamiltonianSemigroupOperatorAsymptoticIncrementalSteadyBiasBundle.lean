import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorVanishingInputDifferencePairwiseAsymptoticIncrementalStabilityBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

private theorem finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal
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

private theorem finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal
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

/-- Exact inverse of the constructed finite Wilson real spectral Hamiltonian. -/
noncomputable def finite_wilson_constructed_real_spectral_hamiltonianInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) : D.StateSpace →L[ℝ] D.StateSpace :=
  orthonormalDiagonalHamiltonianInverse
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)

/-- Constructed left steady response `H⁻¹ Qinf`. -/
noncomputable def finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf : D.StateSpace →L[ℝ] D.StateSpace) :
    D.StateSpace →L[ℝ] D.StateSpace :=
  finite_wilson_constructed_real_spectral_hamiltonianInverse D n * Qinf

/-- Constructed right steady response `Qinf H⁻¹`. -/
noncomputable def finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf : D.StateSpace →L[ℝ] D.StateSpace) :
    D.StateSpace →L[ℝ] D.StateSpace :=
  Qinf * finite_wilson_constructed_real_spectral_hamiltonianInverse D n

/-- The constructed left steady response solves `H W = Qinf`. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf : D.StateSpace →L[ℝ] D.StateSpace) :
    LinearMap.toContinuousLinearMap (D.hamiltonian n) *
      finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf = Qinf := by
  simpa [finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft,
    finite_wilson_constructed_real_spectral_hamiltonianInverse,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    (orthonormalDiagonalHamiltonianSteadyResponseLeft_equilibrium
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf)

/-- The constructed right steady response solves `W H = Qinf` without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf : D.StateSpace →L[ℝ] D.StateSpace) :
    finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf *
      LinearMap.toContinuousLinearMap (D.hamiltonian n) = Qinf := by
  simpa [finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight,
    finite_wilson_constructed_real_spectral_hamiltonianInverse,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    (orthonormalDiagonalHamiltonianSteadyResponseRight_equilibrium
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf)

section Left

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
variable (n : ℕ)
variable (Qinf : D.StateSpace →L[ℝ] D.StateSpace)
variable (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFGinf : Tendsto (fun t : ℝ => ‖(F t - G t) - Qinf‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ, HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ, HasDerivAt V ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)

include n F G hF hG hFGinf hU hV

/-- Constructed left mismatch converges in norm to its exact steady bias. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left :
    Tendsto (fun t : ℝ => ‖(U t - V t) - finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n G V hV)

/-- Constructed left mismatch converges in operator space to its steady response. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_left :
    Tendsto (fun t : ℝ => U t - V t) atTop
      (nhds (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf)) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n G V hV)

/-- Constructed left mismatch converges strongly on each state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_left
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop
      (nhds (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n G V hV) y

/-- Direct constructed left action differences converge to the steady response. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_left
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop
      (nhds (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n G V hV) y

/-- Constructed left matrix-element differences converge to the steady value. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_left
    (x y : D.StateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds (inner ℝ x
        (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y))) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n G V hV) x y

/-- Absolute constructed left matrix elements converge to the absolute steady value. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_left
    (x y : D.StateSpace) :
    Tendsto (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds |inner ℝ x
        (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)|) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n G V hV) x y

/-- One time controls the constructed left steady-bias error on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_left :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y) -
          inner ℝ x (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| < ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_left_deriv_diagonal D n G V hV)

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
variable (n : ℕ)
variable (Qinf : D.StateSpace →L[ℝ] D.StateSpace)
variable (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFGinf : Tendsto (fun t : ℝ => ‖(F t - G t) - Qinf‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ, HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ, HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)

include n F G hF hG hFGinf hU hV

/-- Constructed right mismatch converges in norm to its exact steady bias. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right :
    Tendsto (fun t : ℝ => ‖(U t - V t) - finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖) atTop (nhds 0) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n G V hV)

/-- Constructed right mismatch converges in operator space to its steady response. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_right :
    Tendsto (fun t : ℝ => U t - V t) atTop
      (nhds (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf)) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n G V hV)

/-- Constructed right mismatch converges strongly on each state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_right
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop
      (nhds (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n G V hV) y

/-- Direct constructed right action differences converge to the steady response. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_right
    (y : D.StateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop
      (nhds (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n G V hV) y

/-- Constructed right matrix-element differences converge to the steady value. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_right
    (x y : D.StateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds (inner ℝ x
        (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y))) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n G V hV) x y

/-- Absolute constructed right matrix elements converge to the absolute steady value. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_right
    (x y : D.StateSpace) :
    Tendsto (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds |inner ℝ x
        (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)|) := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n G V hV) x y

/-- One time controls the constructed right steady-bias error on both unit balls. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_right :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y) -
          inner ℝ x (finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| < ε := by
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf F G U V hF hG hFGinf
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n F U hU)
      (finite_wilson_constructed_asymptoticIncrementalSteadyBias_right_deriv_diagonal D n G V hV)

end Right

end

end MathlibAnalytic
end MGAP4D
