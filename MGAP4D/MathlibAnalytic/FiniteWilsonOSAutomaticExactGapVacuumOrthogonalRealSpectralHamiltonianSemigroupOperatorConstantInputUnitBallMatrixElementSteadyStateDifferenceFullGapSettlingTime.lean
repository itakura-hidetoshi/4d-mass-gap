import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputUnitBallMatrixElementSteadyStateDifferenceFullGapSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, left matrix elements settle uniformly over both closed unit balls
    after the exact-gap operator-norm waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ / ε) /
              exactGapValueReal) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x
              (finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U F_lim hU0 hU ε hε

/-- On `Ω⊥`, right matrix elements have the identical uniform unit-ball settling
    time, without a commutation hypothesis. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ / ε) /
              exactGapValueReal) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x
              (finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U F_lim hU0 hU ε hε

end

end MathlibAnalytic
end MGAP4D
