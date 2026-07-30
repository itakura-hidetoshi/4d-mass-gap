import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputFullGapAsymptoticConvergence
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Constructed finite Wilson left constant-input evolution converges to its
steady state at the full exact-gap rate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r) :
    Tendsto U atTop
      (nhds (finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ε' := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    linarith
  refine ⟨t₀ + max 0
      (Real.log
        (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ / ε') /
          exactGapValueReal), ?_⟩
  intro t ht
  have hle :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_left
      D n t₀ A U F_lim hU0 hU ε' hε' t ht
  have hlt :
      ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ < ε := by
    exact lt_of_le_of_lt hle (by dsimp [ε']; linarith)
  simpa [dist_eq_norm] using hlt

/-- Constructed finite Wilson right constant-input evolution has the identical
full exact-gap convergence, without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r) :
    Tendsto U atTop
      (nhds (finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ε' := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    linarith
  refine ⟨t₀ + max 0
      (Real.log
        (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ / ε') /
          exactGapValueReal), ?_⟩
  intro t ht
  have hle :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_right
      D n t₀ A U F_lim hU0 hU ε' hε' t ht
  have hlt :
      ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ < ε := by
    exact lt_of_le_of_lt hle (by dsimp [ε']; linarith)
  simpa [dist_eq_norm] using hlt

end

end MathlibAnalytic
end MGAP4D
