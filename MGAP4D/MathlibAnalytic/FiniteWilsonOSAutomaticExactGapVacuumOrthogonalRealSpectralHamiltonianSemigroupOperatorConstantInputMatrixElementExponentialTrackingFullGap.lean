import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorConstantInputPointwiseExponentialTrackingFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the vacuum-orthogonal sector, every left matrix element of the constant-input
    tracking error decays at the full exact gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F_lim) r) :
    |inner ℝ x
      ((U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim) y)| ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ *
        Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A U F_lim x y hU0 hU

/-- On the vacuum-orthogonal sector, every right matrix element has the same full
    exact-gap estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F_lim) r) :
    |inner ℝ x
      ((U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim) y)| ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ *
        Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A U F_lim x y hU0 hU

end

end MathlibAnalytic
end MGAP4D
