import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorVanishingInputDifferencePairwiseAsymptoticIncrementalStabilityBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorInputProfilePairwiseConvolutionSharpFiniteHorizonBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

section Left

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)
variable (F G U V : ℝ →
  (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFG0 : Tendsto (fun t : ℝ => ‖F t - G t‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U
    ((-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V
    ((-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) * V r + G r) r)

include n F G hF hG hFG0 hU hV

/-- On `Ω⊥`, left trajectories become asymptotically indistinguishable when
their input mismatch vanishes in norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left :
    Tendsto (fun t : ℝ => ‖U t - V t‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F G U V hF hG hFG0 hU hV

/-- On `Ω⊥`, the left operator difference converges to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_left :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds 0) :=
  tendsto_zero_of_tendsto_norm_zero
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left
      D n F G U V hF hG hFG0 hU hV)

/-- On `Ω⊥`, the left operator difference converges strongly on each state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_left
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds 0) :=
  continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_left
      D n F G U V hF hG hFG0 hU hV) y

/-- Direct `Ω⊥` left action differences converge to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_left
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds 0) := by
  simpa using
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_left
      D n F G U V hF hG hFG0 hU hV y)

/-- Every fixed `Ω⊥` left matrix-element difference converges to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_left
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds 0) := by
  have happ :=
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_left
      D n F G U V hF hG hFG0 hU hV y
  have hinner := tendsto_const_nhds.inner happ
  simpa [inner_sub_right] using hinner

/-- Absolute `Ω⊥` left matrix-element differences converge to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_left
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds 0) := by
  have hscalar :=
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_left
      D n F G U V hF hG hFG0 hU hV x y
  simpa [Real.norm_eq_abs] using hscalar.norm

/-- One eventual time controls every `Ω⊥` left matrix element on both unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_left :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| < ε := by
  intro ε hε
  have hnorm :=
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left
      D n F G U V hF hG hFG0 hU hV
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖U t - V t‖ < ε :=
    hnorm.eventually_lt_const hε
  filter_upwards [hsmall] with t ht
  intro x y hx hy
  exact lt_of_le_of_lt
    (continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy) ht

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)
variable (F G U V : ℝ →
  (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFG0 : Tendsto (fun t : ℝ => ‖F t - G t‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U
    (U r * (-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V
    (V r * (-LinearMap.toContinuousLinearMap
      (D.gapData.restrictedHamiltonian n)) + G r) r)

include n F G hF hG hFG0 hU hV

/-- On `Ω⊥`, right trajectories have the same asymptotic incremental stability
without a commutation hypothesis. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right :
    Tendsto (fun t : ℝ => ‖U t - V t‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n F G U V hF hG hFG0 hU hV

/-- On `Ω⊥`, the right operator difference converges to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_right :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds 0) :=
  tendsto_zero_of_tendsto_norm_zero
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right
      D n F G U V hF hG hFG0 hU hV)

/-- On `Ω⊥`, the right operator difference converges strongly on each state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_right
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds 0) :=
  continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_right
      D n F G U V hF hG hFG0 hU hV) y

/-- Direct `Ω⊥` right action differences converge to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_right
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds 0) := by
  simpa using
    (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_right
      D n F G U V hF hG hFG0 hU hV y)

/-- Every fixed `Ω⊥` right matrix-element difference converges to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_right
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds 0) := by
  have happ :=
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_right
      D n F G U V hF hG hFG0 hU hV y
  have hinner := tendsto_const_nhds.inner happ
  simpa [inner_sub_right] using hinner

/-- Absolute `Ω⊥` right matrix-element differences converge to zero. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_right
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds 0) := by
  have hscalar :=
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_right
      D n F G U V hF hG hFG0 hU hV x y
  simpa [Real.norm_eq_abs] using hscalar.norm

/-- One eventual time controls every `Ω⊥` right matrix element on both unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_right :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| < ε := by
  intro ε hε
  have hnorm :=
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right
      D n F G U V hF hG hFG0 hU hV
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖U t - V t‖ < ε :=
    hnorm.eventually_lt_const hε
  filter_upwards [hsmall] with t ht
  intro x y hx hy
  exact lt_of_le_of_lt
    (continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy) ht

end Right

end

end MathlibAnalytic
end MGAP4D
