import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputFullGapAsymptoticConvergence
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGapSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- On `Ω⊥`, left constant-input evolution converges to its steady state at the
full exact-gap rate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F_lim) r) :
    Tendsto U atTop
      (nhds (finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U F_lim hU0 hU

/-- On `Ω⊥`, right constant-input evolution has the same full exact-gap
convergence, without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F_lim) r) :
    Tendsto U atTop
      (nhds (finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U F_lim hU0 hU

end

end MathlibAnalytic
end MGAP4D
