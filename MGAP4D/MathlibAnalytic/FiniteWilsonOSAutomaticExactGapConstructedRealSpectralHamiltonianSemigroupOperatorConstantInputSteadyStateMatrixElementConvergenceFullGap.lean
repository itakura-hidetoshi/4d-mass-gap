import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputSteadyStateMatrixElementConvergenceFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputWeakMatrixElementConvergenceFullGap

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Constructed finite Wilson left constant-input evolution converges in every
    scalar matrix element directly to its steady state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_tendsto_steadyState_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y)) atTop
      (nhds (inner ℝ x
        (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim y))) := by
  exact continuousLinearMap_tendsto_inner_apply_of_tendsto
    U (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) x y
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
      D n t₀ A U F_lim hU0 hU)

/-- Constructed finite Wilson right constant-input evolution has the identical
    steady-state matrix-element convergence, without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_tendsto_steadyState_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y)) atTop
      (nhds (inner ℝ x
        (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim y))) := by
  exact continuousLinearMap_tendsto_inner_apply_of_tendsto
    U (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) x y
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
      D n t₀ A U F_lim hU0 hU)

end

end MathlibAnalytic
end MGAP4D
