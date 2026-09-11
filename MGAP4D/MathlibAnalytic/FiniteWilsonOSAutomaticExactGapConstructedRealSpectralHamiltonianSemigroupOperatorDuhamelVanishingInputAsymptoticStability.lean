import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelVanishingInputAsymptoticStability
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingPracticalSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- Constructed finite Wilson left evolution is asymptotically stable under any
continuous forcing whose operator norm vanishes at large time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      F U hF hF0 hUdiag

/-- Constructed finite Wilson right evolution has the same vanishing-input
operator-norm stability without a commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n]
      using hU r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos
      F U hF hF0 hUdiag

/-- Constructed finite Wilson left vanishing-input evolution converges to zero in
operator space. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    Tendsto U atTop (nhds 0) := by
  exact tendsto_zero_of_tendsto_norm_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      D n F U hF hF0 hU)

/-- Constructed finite Wilson right vanishing-input evolution converges to zero
in operator space. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    Tendsto U atTop (nhds 0) := by
  exact tendsto_zero_of_tendsto_norm_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      D n F U hF hF0 hU)

/-- Constructed finite Wilson left vanishing-input evolution converges strongly
to zero on every fixed state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (x : D.StateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
      D n F U hF hF0 hU) x

/-- Constructed finite Wilson right vanishing-input evolution converges strongly
to zero on every fixed state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_apply_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (x : D.StateSpace) :
    Tendsto (fun t : ℝ => U t x) atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
      D n F U hF hF0 hU) x

/-- Constructed finite Wilson left vanishing-input evolution converges uniformly
to zero on the closed unit ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∀ x : D.StateSpace, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_left
      D n F U hF hF0 hU)

/-- Constructed finite Wilson right vanishing-input evolution converges uniformly
to zero on the closed unit ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_eventually_uniform_unitBall_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hF : Continuous F)
    (hF0 : Tendsto (fun t : ℝ => ‖F t‖) atTop (nhds 0))
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∀ x : D.StateSpace, ‖x‖ ≤ 1 → ‖U t x‖ < ε := by
  exact continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_zero_right
      D n F U hF hF0 hU)

end

end MathlibAnalytic
end MGAP4D
