import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelVanishingInputAsymptoticStability
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorInputProfilePairwiseConvolutionSharpFiniteHorizonBundle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

private theorem orthonormalDiagonal_vanishingInputDifference_pairwise_left_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((-orthonormalDiagonalOperator b a) * (U r - V r) +
          (F r - G r)) r := by
  intro r
  have hsub := (hU r).sub (hV r)
  convert hsub using 1
  noncomm_ring

private theorem orthonormalDiagonal_vanishingInputDifference_pairwise_right_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((U r - V r) * (-orthonormalDiagonalOperator b a) +
          (F r - G r)) r := by
  intro r
  have hsub := (hU r).sub (hV r)
  convert hsub using 1
  noncomm_ring

private theorem tendsto_real_inner_const_of_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) {f : ℝ → E}
    (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (fun t : ℝ => inner ℝ x (f t)) atTop (nhds 0) := by
  have hx : Tendsto (fun _ : ℝ => x) atTop (nhds x) := tendsto_const_nhds
  simpa using hx.inner hf

private theorem eventually_uniform_unitBall_matrixElement_difference_of_tendsto_norm_sub_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U V : ℝ → (E →L[ℝ] E))
    (hUV : Tendsto (fun t : ℝ => ‖U t - V t‖) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| < ε := by
  intro ε hε
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖U t - V t‖ < ε :=
    hUV.eventually_lt_const hε
  filter_upwards [hsmall] with t ht
  intro x y hx hy
  exact lt_of_le_of_lt
    (continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy) ht

section Left

variable {ι E : Type*}
variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
variable (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
variable (F G U V : ℝ → (E →L[ℝ] E))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFG0 : Tendsto (fun t : ℝ => ‖F t - G t‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)

include hδ hδpos F G hF hG hFG0 hU hV

/-- If the norm of the left input mismatch vanishes, the operator distance
between the trajectories vanishes. Neither input needs to converge separately. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left :
    Tendsto (fun t : ℝ => ‖U t - V t‖) atTop (nhds 0) := by
  have hQ : Continuous (fun t : ℝ => F t - G t) := hF.sub hG
  simpa using
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      b a δ hδ hδpos
      (fun t : ℝ => F t - G t) (fun t : ℝ => U t - V t)
      hQ hFG0
      (orthonormalDiagonal_vanishingInputDifference_pairwise_left_deriv
        b a F G U V hU hV))

/-- The left operator difference converges to zero in operator space. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_left :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds 0) :=
  tendsto_zero_of_tendsto_norm_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV)

/-- The left operator difference converges strongly on each fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_left
    (y : E) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds 0) :=
  continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_left
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV) y

/-- Direct left action differences converge to zero on every fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_left
    (y : E) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds 0) := by
  simpa using
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_left
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV y)

/-- Every fixed left matrix-element difference converges to zero. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_left
    (x y : E) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds 0) := by
  have happ :=
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_left
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV y
  have hinner := tendsto_real_inner_const_of_tendsto_zero x happ
  simpa [inner_sub_right] using hinner

/-- The absolute value of every fixed left matrix-element difference tends to zero. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_left
    (x y : E) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds 0) := by
  have hscalar :=
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_left
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV x y
  simpa [Real.norm_eq_abs] using hscalar.norm

/-- One eventual time controls every left matrix element on both unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_left :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| < ε :=
  eventually_uniform_unitBall_matrixElement_difference_of_tendsto_norm_sub_zero
    U V
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_left
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV)

end Left

section Right

variable {ι E : Type*}
variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
variable (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
variable (F G U V : ℝ → (E →L[ℝ] E))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFG0 : Tendsto (fun t : ℝ => ‖F t - G t‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)

include hδ hδpos F G hF hG hFG0 hU hV

/-- Right multiplication has the same asymptotic incremental stability without
any commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right :
    Tendsto (fun t : ℝ => ‖U t - V t‖) atTop (nhds 0) := by
  have hQ : Continuous (fun t : ℝ => F t - G t) := hF.sub hG
  simpa using
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      b a δ hδ hδpos
      (fun t : ℝ => F t - G t) (fun t : ℝ => U t - V t)
      hQ hFG0
      (orthonormalDiagonal_vanishingInputDifference_pairwise_right_deriv
        b a F G U V hU hV))

/-- The right operator difference converges to zero in operator space. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_right :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds 0) :=
  tendsto_zero_of_tendsto_norm_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV)

/-- The right operator difference converges strongly on each fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_right
    (y : E) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds 0) :=
  continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_sub_zero_right
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV) y

/-- Direct right action differences converge to zero on every fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_right
    (y : E) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds 0) := by
  simpa using
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_sub_zero_right
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV y)

/-- Every fixed right matrix-element difference converges to zero. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_right
    (x y : E) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds 0) := by
  have happ :=
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_apply_difference_zero_right
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV y
  have hinner := tendsto_real_inner_const_of_tendsto_zero x happ
  simpa [inner_sub_right] using hinner

/-- The absolute value of every fixed right matrix-element difference tends to zero. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_abs_matrixElement_difference_zero_right
    (x y : E) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds 0) := by
  have hscalar :=
    orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_matrixElement_difference_zero_right
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV x y
  simpa [Real.norm_eq_abs] using hscalar.norm

/-- One eventual time controls every right matrix element on both unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_eventually_uniform_unitBall_matrixElement_difference_zero_right :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| < ε :=
  eventually_uniform_unitBall_matrixElement_difference_of_tendsto_norm_sub_zero
    U V
    (orthonormalDiagonalHamiltonianSemigroup_operator_vanishingInputDifference_pairwise_tendsto_norm_sub_zero_right
      b a δ hδ hδpos F G U V hF hG hFG0 hU hV)

end Right

end

end MathlibAnalytic
end MGAP4D
