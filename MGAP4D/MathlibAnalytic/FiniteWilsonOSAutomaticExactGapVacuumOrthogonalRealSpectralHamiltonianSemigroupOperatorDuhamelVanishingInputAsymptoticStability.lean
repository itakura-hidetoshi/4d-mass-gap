import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelVanishingInputAsymptoticStability
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingPracticalSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- On the physical excitation sector `Ω⊥`, left vanishing-input evolution has
operator norm converging to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU

/-- On `Ω⊥`, right vanishing-input evolution has the same operator-norm
convergence. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU

/-- On `Ω⊥`, left vanishing-input evolution converges to zero in operator space. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    Tendsto U atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU

/-- On `Ω⊥`, right vanishing-input evolution converges to zero in operator space. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    Tendsto U atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU

/-- On `Ω⊥`, left vanishing-input evolution converges strongly to zero on every
fixed excitation state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (x : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU x

/-- On `Ω⊥`, right vanishing-input evolution converges strongly to zero on every
fixed excitation state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r)
    (x : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU x

/-- On `Ω⊥`, left vanishing-input evolution converges uniformly to zero on the
closed unit ball of the excitation sector. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∀ x : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU

/-- On `Ω⊥`, right vanishing-input evolution converges uniformly to zero on the
closed unit ball of the excitation sector. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∀ x : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U hF hF0 hU

end

end MathlibAnalytic
end MGAP4D
