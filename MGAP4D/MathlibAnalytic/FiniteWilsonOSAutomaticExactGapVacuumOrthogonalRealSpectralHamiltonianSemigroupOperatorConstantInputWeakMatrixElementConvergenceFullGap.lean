import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputWeakMatrixElementConvergenceFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorConstantInputFullGapAsymptoticConvergence

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- On `Ω⊥`, left constant-input evolution converges weakly in every scalar matrix
    element to its exact-gap steady state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_weakMatrixElement_tendsto_zero_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F_lim) r) :
    Tendsto
      (fun t : ℝ => inner ℝ x
        ((U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim) y))
      atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto
    U (finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim) x y
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
      D n t₀ A U F_lim hU0 hU)

/-- On `Ω⊥`, right constant-input evolution has the same weak matrix-element
    convergence, without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_weakMatrixElement_tendsto_zero_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F_lim) r) :
    Tendsto
      (fun t : ℝ => inner ℝ x
        ((U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim) y))
      atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto
    U (finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim) x y
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
      D n t₀ A U F_lim hU0 hU)

end

end MathlibAnalytic
end MGAP4D
