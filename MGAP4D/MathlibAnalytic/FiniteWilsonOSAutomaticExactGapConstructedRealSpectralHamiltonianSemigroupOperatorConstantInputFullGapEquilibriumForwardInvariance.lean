import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputFullGapEquilibriumForwardInvariance
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left evolution initialized at its constant-input
steady state remains there for all later times. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_eq_steadyState_of_initial_eq_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r)
    (hA : A = finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) :
    U t = finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim := by
  have henv :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_left
      D n t₀ t ht A U F_lim hU0 hU
  have hzero :
      ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤ 0 := by
    simpa [hA] using henv
  have hnorm :
      ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ = 0 :=
    le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Constructed finite Wilson right evolution initialized at its constant-input
steady state is forward invariant, without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_eq_steadyState_of_initial_eq_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r)
    (hA : A = finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) :
    U t = finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim := by
  have henv :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_right
      D n t₀ t ht A U F_lim hU0 hU
  have hzero :
      ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤ 0 := by
    simpa [hA] using henv
  have hnorm :
      ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ = 0 :=
    le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end

end MathlibAnalytic
end MGAP4D
