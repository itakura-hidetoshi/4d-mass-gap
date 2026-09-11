import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGapSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, left constant-input matrix elements reach every positive tolerance
    after the explicit exact-gap logarithmic waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_left
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
        (D.gapData.restrictedHamiltonian n)) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim) y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U F_lim x y hU0 hU ε hε

/-- On `Ω⊥`, right constant-input matrix elements have the identical explicit
    settling time, without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_right
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
        (D.gapData.restrictedHamiltonian n)) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim) y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U F_lim x y hU0 hU ε hε

end

end MathlibAnalytic
end MGAP4D
