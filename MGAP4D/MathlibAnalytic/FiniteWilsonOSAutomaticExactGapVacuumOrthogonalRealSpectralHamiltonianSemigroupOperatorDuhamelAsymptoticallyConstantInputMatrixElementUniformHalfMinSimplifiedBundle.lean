import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputMatrixElementUniformHalfMinSimplifiedBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplifiedSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, left pointwise tracking has the exact-gap half-min estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ‖(U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim) y‖ ≤
      ((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A F U F_lim C hC hF hFC y hU0 hU

/-- On `Ω⊥`, right pointwise tracking has the identical estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖(U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim) y‖ ≤
      ((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_pointwise_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A F U F_lim C hC hF hFC y hU0 hU

/-- On `Ω⊥`, left matrix-element tracking has the exact-gap half-min estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    |inner ℝ x
      ((U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim) y)| ≤
      ((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A F U F_lim C hC hF hFC x y hU0 hU

/-- On `Ω⊥`, right matrix-element tracking has the identical estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r) :
    |inner ℝ x
      ((U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim) y)| ≤
      ((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
          2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A F U F_lim C hC hF hFC x y hU0 hU

/-- On `Ω⊥`, left matrix-element tracking reaches every tolerance after the explicit
    vector-dependent waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim) y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hU ε hε

/-- On `Ω⊥`, right matrix-element tracking has the identical settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim) y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hU ε hε

/-- On `Ω⊥`, left matrix elements reach the steady-state value after the explicit
    vector-dependent waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hU ε hε

/-- On `Ω⊥`, right matrix elements have the identical direct settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace) (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) -
          inner ℝ x (finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A F U F_lim C hC hF hFC x y hU0 hU ε hε

/-- On `Ω⊥`, one half-min waiting time works uniformly for all left matrix elements
    on both closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) / ε) /
              (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

/-- On `Ω⊥`, the right action has the identical uniform unit-ball waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / max exactGapValueReal μ) / ε) /
              (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

end

end MathlibAnalytic
end MGAP4D
