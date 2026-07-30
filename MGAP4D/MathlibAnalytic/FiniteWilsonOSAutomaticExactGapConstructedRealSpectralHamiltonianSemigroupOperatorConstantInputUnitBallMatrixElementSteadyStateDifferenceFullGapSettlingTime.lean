import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputUnitBallMatrixElementSteadyStateDifferenceFullGapSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGapSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left matrix elements settle uniformly over both
    closed unit balls after the exact-gap operator-norm waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ / ε) /
              exactGapValueReal) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) x y hx hy
  exact hmatrix.trans
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_left
      D n t₀ A U F_lim hU0 hU ε hε t ht)

/-- Constructed finite Wilson right matrix elements have the identical uniform
    unit-ball settling time and require no commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ / ε) /
              exactGapValueReal) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) x y hx hy
  exact hmatrix.trans
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_right
      D n t₀ A U F_lim hU0 hU ε hε t ht)

end

end MathlibAnalytic
end MGAP4D
