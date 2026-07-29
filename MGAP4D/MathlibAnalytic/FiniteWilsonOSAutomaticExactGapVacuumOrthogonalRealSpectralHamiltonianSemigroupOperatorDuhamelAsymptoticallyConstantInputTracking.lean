import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputTracking
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelVanishingInputAsymptoticStability

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- The explicit inverse of the restricted Hamiltonian on `Ω⊥`. -/
noncomputable def finiteWilsonVacuumOrthogonalHamiltonianInverseOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finiteWilsonConstructedHamiltonianInverseOperator
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The left stationary response on `Ω⊥`. -/
noncomputable def finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finiteWilsonConstructedHamiltonianLeftSteadyState
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n F∞

/-- The right stationary response on `Ω⊥`. -/
noncomputable def finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finiteWilsonConstructedHamiltonianRightSteadyState
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n F∞

/-- The restricted Hamiltonian inverse is a right inverse on `Ω⊥`. -/
theorem finite_wilson_vacuum_orthogonal_hamiltonian_mul_inverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) *
        finiteWilsonVacuumOrthogonalHamiltonianInverseOperator D n = 1 := by
  exact finite_wilson_constructed_hamiltonian_mul_inverse
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The restricted Hamiltonian inverse is also a left inverse on `Ω⊥`. -/
theorem finite_wilson_vacuum_orthogonal_inverse_mul_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    finiteWilsonVacuumOrthogonalHamiltonianInverseOperator D n *
        LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) = 1 := by
  exact finite_wilson_constructed_inverse_mul_hamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The left steady response on `Ω⊥` solves the stationary equation. -/
theorem finite_wilson_vacuum_orthogonal_hamiltonian_leftSteadyState_stationary
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) *
        finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F∞ = F∞ := by
  exact finite_wilson_constructed_hamiltonian_leftSteadyState_stationary
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n F∞

/-- The right steady response on `Ω⊥` solves the stationary equation. -/
theorem finite_wilson_vacuum_orthogonal_hamiltonian_rightSteadyState_stationary
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F∞ *
        LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) = F∞ := by
  exact finite_wilson_constructed_hamiltonian_rightSteadyState_stationary
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n F∞

/-- The left stationary response on `Ω⊥` is unique. -/
theorem finite_wilson_vacuum_orthogonal_hamiltonian_leftSteadyState_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F∞ S : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hS : LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) * S = F∞) :
    S = finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F∞ := by
  exact finite_wilson_constructed_hamiltonian_leftSteadyState_unique
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n F∞ S hS

/-- The right stationary response on `Ω⊥` is unique. -/
theorem finite_wilson_vacuum_orthogonal_hamiltonian_rightSteadyState_unique
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F∞ S : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hS : S * LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) = F∞) :
    S = finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F∞ := by
  exact finite_wilson_constructed_hamiltonian_rightSteadyState_unique
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n F∞ S hS

/-- On `Ω⊥`, left evolution tracks its unique stationary response in operator norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    Tendsto
      (fun t : ℝ =>
        ‖U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F∞‖)
      atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU

/-- On `Ω⊥`, right evolution tracks its unique stationary response in operator norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    Tendsto
      (fun t : ℝ =>
        ‖U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F∞‖)
      atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU

/-- On `Ω⊥`, left evolution converges in operator space to the steady response. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_leftSteadyState_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    Tendsto U atTop
      (nhds (finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F∞)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_leftSteadyState_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU

/-- On `Ω⊥`, right evolution converges in operator space to the steady response. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_rightSteadyState_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    Tendsto U atTop
      (nhds (finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F∞)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_rightSteadyState_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU

/-- On `Ω⊥`, left tracking holds strongly on every fixed excitation state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (x : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F∞ x)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU x

/-- On `Ω⊥`, right tracking holds strongly on every fixed excitation state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r)
    (x : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F∞ x)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU x

/-- On `Ω⊥`, left tracking is uniform on the closed unit ball. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 →
        ‖U t x - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F∞ x‖ < ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU

/-- On `Ω⊥`, right tracking is uniform on the closed unit ball. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F∞ : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 →
        ‖U t x - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F∞ x‖ < ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F U F∞ hF hF∞ hU

end

end MathlibAnalytic
end MGAP4D
