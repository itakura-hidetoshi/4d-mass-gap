import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputWeakMatrixElementConvergenceFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputFullGapAsymptoticConvergence

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Constructed finite Wilson left constant-input evolution converges weakly, in
    every scalar matrix element, to its steady state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_weakMatrixElement_tendsto_zero_fullGap_left
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
    Tendsto
      (fun t : ℝ => inner ℝ x
        ((U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y))
      atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto
    U (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) x y
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
      D n t₀ A U F_lim hU0 hU)

/-- Constructed finite Wilson right constant-input evolution has the identical
    weak matrix-element convergence, without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_weakMatrixElement_tendsto_zero_fullGap_right
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
    Tendsto
      (fun t : ℝ => inner ℝ x
        ((U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y))
      atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto
    U (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) x y
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
      D n t₀ A U F_lim hU0 hU)

end

end MathlibAnalytic
end MGAP4D
