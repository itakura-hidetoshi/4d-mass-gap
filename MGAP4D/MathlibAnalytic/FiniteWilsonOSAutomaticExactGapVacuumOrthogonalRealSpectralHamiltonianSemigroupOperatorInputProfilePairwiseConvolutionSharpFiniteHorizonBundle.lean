import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorInputProfilePairwiseConvolutionSharpFiniteHorizonBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorBoundedInputDifferencePairwiseInputToStateBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

section Left

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ) (t₀ : ℝ)
variable (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U ((-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V ((-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) * V r + G r) r)

include n F G hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, left trajectories retain the complete input-difference convolution. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, left convolution control acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_left
    (t : ℝ) (ht : t₀ ≤ t) (y : D.gapData.ExcitedStateSpace) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG y hU0 hV0 hU hV

/-- On `Ω⊥`, left matrix elements retain the complete convolution. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_left
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG x y hU0 hV0 hU hV

/-- On `Ω⊥`, direct left matrix-element differences retain the convolution. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_left
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG x y hU0 hV0 hU hV

/-- On `Ω⊥`, one left convolution bound controls both closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_left
    (t : ℝ) (ht : t₀ ≤ t) :
    ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, bounded left input mismatch has the sharp finite-horizon gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_left
    (t : ℝ) (ht : t₀ ≤ t)
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ) (t₀ : ℝ)
variable (A B : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
    (D.gapData.restrictedHamiltonian n)) + G r) r)

include n F G hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, right trajectories retain the complete input-difference convolution. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
    (t : ℝ) (ht : t₀ ≤ t) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, right convolution control acts pointwise. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_right
    (t : ℝ) (ht : t₀ ≤ t) (y : D.gapData.ExcitedStateSpace) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG y hU0 hV0 hU hV

/-- On `Ω⊥`, right matrix elements retain the complete convolution. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_right
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG x y hU0 hV0 hU hV

/-- On `Ω⊥`, direct right matrix-element differences retain the convolution. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_right
    (t : ℝ) (ht : t₀ ≤ t) (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG x y hU0 hV0 hU hV

/-- On `Ω⊥`, one right convolution bound controls both closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_right
    (t : ℝ) (ht : t₀ ≤ t) :
    ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) * ‖F s - G s‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, bounded right input mismatch has the sharp finite-horizon gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_right
    (t : ℝ) (ht : t₀ ≤ t)
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A - B‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV

end Right

/-- On `Ω⊥`, equal-initial left trajectories have pure finite-horizon input gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * V r + G r) r) :
    ‖U t - V t‖ ≤
      ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F G U V C hC hF hG hFG hU0 hV0 hU hV

/-- On `Ω⊥`, equal-initial right trajectories have pure finite-horizon input gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F G U V : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + G r) r) :
    ‖U t - V t‖ ≤
      ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F G U V C hC hF hG hFG hU0 hV0 hU hV

end

end MathlibAnalytic
end MGAP4D