import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelZeroInputOperatorStrongConvergence
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelZeroInputNormConvergence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- Constructed finite Wilson left zero-input evolution converges to zero in the
continuous-linear-operator space. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r) r) :
    Tendsto U atTop (nhds 0) := by
  exact
    tendsto_zero_of_tendsto_norm_zero
      (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_left
        D n t₀ A U hU0 hU)

/-- Constructed finite Wilson right zero-input evolution converges to zero in
operator space, without a commutation hypothesis on the initial operator. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n))) r) :
    Tendsto U atTop (nhds 0) := by
  exact
    tendsto_zero_of_tendsto_norm_zero
      (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_right
        D n t₀ A U hU0 hU)

/-- Constructed finite Wilson left zero-input evolution converges strongly on
every fixed state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_apply_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r) r)
    (x : D.StateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact
    continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
      (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_left
        D n t₀ A U hU0 hU) x

/-- Constructed finite Wilson right zero-input evolution converges strongly on
every fixed state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_apply_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n))) r)
    (x : D.StateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact
    continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
      (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_right
        D n t₀ A U hU0 hU) x

/-- Constructed finite Wilson left zero-input evolution converges uniformly on
the closed unit ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_eventually_uniform_unitBall_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∀ x : D.StateSpace, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact
    continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
      (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_left
        D n t₀ A U hU0 hU)

/-- Constructed finite Wilson right zero-input evolution converges uniformly on
the closed unit ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_eventually_uniform_unitBall_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n))) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∀ x : D.StateSpace, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact
    continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
      (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_zero_right
        D n t₀ A U hU0 hU)

end

end MathlibAnalytic
end MGAP4D
