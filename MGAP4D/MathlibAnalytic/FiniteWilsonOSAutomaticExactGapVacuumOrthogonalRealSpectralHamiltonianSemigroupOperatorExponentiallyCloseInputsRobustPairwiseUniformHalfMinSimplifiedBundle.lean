import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorExponentiallyCloseInputsRobustPairwiseUniformHalfMinSimplifiedBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputMatrixElementUniformHalfMinSimplifiedBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, left trajectories with exponentially close inputs obey the robust
    exact-gap half-min envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r) :
    ‖U t - V t‖ ≤
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2))) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV

/-- On `Ω⊥`, the right robust envelope is identical. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r) :
    ‖U t - V t‖ ≤
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2))) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV

/-- On `Ω⊥`, left operator distance has the explicit robust waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, right operator distance has the identical waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, left robust tracking acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r) :
    ‖(U t - V t) y‖ ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV

/-- On `Ω⊥`, right robust tracking acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r) :
    ‖(U t - V t) y‖ ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV

/-- On `Ω⊥`, left pairwise matrix elements obey the robust envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, right pairwise matrix elements obey the same robust envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, left direct matrix-element differences obey the robust envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, right direct matrix-element differences obey the same envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- On `Ω⊥`, left fixed matrix elements have the robust settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, right fixed matrix elements have the same robust settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, left unit-ball matrix elements settle uniformly. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, right unit-ball matrix elements settle uniformly. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε

end

end MathlibAnalytic
end MGAP4D
