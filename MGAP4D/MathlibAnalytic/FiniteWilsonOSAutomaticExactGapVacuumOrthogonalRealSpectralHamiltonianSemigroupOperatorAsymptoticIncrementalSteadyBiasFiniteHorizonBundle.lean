import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasFiniteHorizonBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

section Left

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
variable (A B Qinf :
  D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ →
  (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U
    ((-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V
    ((-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) * V r + G r) r)

include n ht hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, the left affine error retains the complete residual profile. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left :
    ‖(U t - V t) -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, the left affine estimate acts on every state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_left
    (y : D.gapData.ExcitedStateSpace) :
    ‖U t y - V t y -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV y

/-- On `Ω⊥`, every left matrix-element error retains the complete residual profile. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_left
    (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV x y

/-- One left `Ω⊥` profile bound controls both closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_left :
    ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
            ‖(F s - G s) - Qinf‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, bounded left residuals have the sharp finite-horizon gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ‖(U t - V t) -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG

/-- Sharp left residual control on every `Ω⊥` state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (y : D.gapData.ExcitedStateSpace) :
    ‖U t y - V t y -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG y

/-- Sharp left residual control for every `Ω⊥` matrix element. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG x y

/-- One sharp left `Ω⊥` residual bound controls both closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ +
          ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
variable (A B Qinf :
  D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ →
  (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U
    (U r * (-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V
    (V r * (-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) + G r) r)

include n ht hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, the right affine error retains the complete profile without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right :
    ‖(U t - V t) -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, the right affine estimate acts on every state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_right
    (y : D.gapData.ExcitedStateSpace) :
    ‖U t y - V t y -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV y

/-- On `Ω⊥`, every right matrix-element error retains the complete residual profile. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_right
    (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV x y

/-- One right `Ω⊥` profile bound controls both closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_right :
    ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * exactGapValueReal)) *
            ‖(F s - G s) - Qinf‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV

/-- On `Ω⊥`, bounded right residuals have the sharp gain without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ‖(U t - V t) -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG

/-- Sharp right residual control on every `Ω⊥` state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (y : D.gapData.ExcitedStateSpace) :
    ‖U t y - V t y -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y‖ ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG y

/-- Sharp right residual control for every `Ω⊥` matrix element. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (x y : D.gapData.ExcitedStateSpace) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
      (Real.exp (-((t - t₀) * exactGapValueReal)) *
          ‖(A - B) -
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C) * ‖x‖ * ‖y‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG x y

/-- One sharp right `Ω⊥` residual bound controls both closed unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| ≤
        Real.exp (-((t - t₀) * exactGapValueReal)) *
            ‖(A - B) -
              finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ +
          ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) / exactGapValueReal) * C := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV C hC hFG

end Right

end

end MathlibAnalytic
end MGAP4D
