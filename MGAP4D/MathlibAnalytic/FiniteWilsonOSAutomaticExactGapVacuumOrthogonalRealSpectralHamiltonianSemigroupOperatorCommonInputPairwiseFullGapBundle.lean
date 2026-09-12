import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorCommonInputPairwiseFullGapBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, two left trajectories driven by the same arbitrary input contract at
    the full exact-gap rate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F hU0 hV0 hU hV

/-- On `Ω⊥`, two right trajectories have the identical full exact-gap estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F hU0 hV0 hU hV

/-- On `Ω⊥`, left pairwise operator distance has an explicit exact-gap settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B U V F hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, right pairwise operator distance has the identical waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B U V F hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, left pairwise contraction acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F y hU0 hV0 hU hV

/-- On `Ω⊥`, right pairwise contraction acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F y hU0 hV0 hU hV

/-- On `Ω⊥`, every left pairwise matrix element contracts at the exact gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F x y hU0 hV0 hU hV

/-- On `Ω⊥`, every right pairwise matrix element has the same estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F x y hU0 hV0 hU hV

/-- On `Ω⊥`, left pairwise matrix elements have an explicit vector-dependent
    exact-gap settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x ((U t - V t) y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B U V F x y hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, right pairwise matrix elements have the same explicit waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (x y : D.gapData.ExcitedStateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x ((U t - V t) y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B U V F x y hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, left pairwise matrix elements settle uniformly on both unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B U V F hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, right pairwise matrix elements have the same unit-ball waiting time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A B U V F hU0 hV0 hU hV ε hε

/-- On `Ω⊥`, left evolution under a common arbitrary input is forward unique. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + F r) r)
    (hAB : A = B) :
    U t = V t := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F hU0 hV0 hU hV hAB

/-- On `Ω⊥`, right evolution has the same forward uniqueness. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hAB : A = B) :
    U t = V t := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B U V F hU0 hV0 hU hV hAB

end

end MathlibAnalytic
end MGAP4D
