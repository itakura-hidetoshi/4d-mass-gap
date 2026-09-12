import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementSteadyStateDifferenceFullGapSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGapSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left matrix elements approach their steady-state
    values within every positive tolerance after the exact-gap waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim y)| ≤ ε := by
  intro t ht
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_left
      D n t₀ A U F_lim x y hU0 hU ε hε t ht

/-- Constructed finite Wilson right matrix elements have the identical direct
    steady-state settling time and require no commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim y)| ≤ ε := by
  intro t ht
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_right
      D n t₀ A U F_lim x y hU0 hU ε hε t ht

end

end MathlibAnalytic
end MGAP4D
