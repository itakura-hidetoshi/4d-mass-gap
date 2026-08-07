import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementKernelCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Two finite boundary vectors with the same pairwise differences have the same
uniform-average complement. -/
theorem finiteUniformAverageComplementLinearMap_eq_of_pairwise_sub_eq
    {α : Type} [Fintype α] [Nonempty α]
    (g h : FiniteBoundaryHilbert α)
    (hsub : ∀ y y' : α, g y - g y' = h y - h y') :
    finiteUniformAverageComplementLinearMap g =
      finiteUniformAverageComplementLinearMap h := by
  have hconst : ∀ y y' : α, (g - h) y = (g - h) y' := by
    intro y y'
    change g y - h y = g y' - h y'
    have hs := hsub y y'
    linarith
  have hz :=
    finiteUniformAverageComplementLinearMap_eq_zero_of_constant
      (g - h) hconst
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Canonical first-order kernel at a uniform beta-zero fixed point when the
raw first variation is boundary-additive with the same one-half spatial term on
both boundaries.  The beta-zero normalization value is exactly `1 / |α|`;
`normalizationDerivative` is arbitrary. -/
noncomputable def finiteUniformNormalizedAdditiveFirstVariationKernel
    {α : Type} [Fintype α]
    (spatial : α → ℝ)
    (crossingMean normalizationDerivative : ℝ)
    (x y : α) : ℝ :=
  -(Fintype.card α : ℝ)⁻¹ *
      ((1 / 2 : ℝ) * spatial x + crossingMean +
        (1 / 2 : ℝ) * spatial y) +
    normalizationDerivative

/-- Spatial rank-one kernel appearing in the normalized beta-zero slab second
variation. -/
noncomputable def finiteUniformNormalizedSpatialRankOneKernel
    {α : Type} [Fintype α]
    (spatial : α → ℝ)
    (x y : α) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) * spatial x * spatial y

/-- On a zero-mass input, the normalized additive first-variation kernel has
constant output. -/
theorem finiteUniformNormalizedAdditiveFirstVariationKernel_apply_complement
    {α : Type} [Fintype α] [Nonempty α]
    (spatial : α → ℝ)
    (crossingMean normalizationDerivative : ℝ)
    (f : FiniteBoundaryHilbert α)
    (y : α) :
    finiteKernelOperator
        (finiteUniformNormalizedAdditiveFirstVariationKernel
          spatial crossingMean normalizationDerivative)
        (finiteUniformAverageComplementLinearMap f) y =
      -(Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) *
        ∑ x : α, spatial x * finiteUniformAverageComplementLinearMap f x := by
  classical
  have hsum := finiteUniformAverageComplementLinearMap_sum_apply f
  rw [finiteKernelOperator_apply]
  unfold finiteUniformNormalizedAdditiveFirstVariationKernel
  calc
    (∑ x : α,
      (-(Fintype.card α : ℝ)⁻¹ *
            ((1 / 2 : ℝ) * spatial x + crossingMean +
              (1 / 2 : ℝ) * spatial y) +
          normalizationDerivative) *
        finiteUniformAverageComplementLinearMap f x) =
      ∑ x : α, (
        (-(Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ)) *
            (spatial x * finiteUniformAverageComplementLinearMap f x) +
          (-(Fintype.card α : ℝ)⁻¹ *
              (crossingMean + (1 / 2 : ℝ) * spatial y) +
            normalizationDerivative) *
            finiteUniformAverageComplementLinearMap f x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        ring
    _ =
      (-(Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ)) *
          (∑ x : α,
            spatial x * finiteUniformAverageComplementLinearMap f x) +
        (-(Fintype.card α : ℝ)⁻¹ *
              (crossingMean + (1 / 2 : ℝ) * spatial y) +
            normalizationDerivative) *
          (∑ x : α, finiteUniformAverageComplementLinearMap f x) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by
      rw [hsum, mul_zero, add_zero]

/-- Uniform projection does nothing to the constant output produced after the
first complemented application. -/
theorem finiteUniformAverageProjectorLinearMap_comp_additiveFirstVariation_apply_complement
    {α : Type} [Fintype α] [Nonempty α]
    (spatial : α → ℝ)
    (crossingMean normalizationDerivative : ℝ)
    (f : FiniteBoundaryHilbert α)
    (y : α) :
    finiteUniformAverageProjectorLinearMap
        (finiteKernelOperator
          (finiteUniformNormalizedAdditiveFirstVariationKernel
            spatial crossingMean normalizationDerivative)
          (finiteUniformAverageComplementLinearMap f)) y =
      -(Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) *
        ∑ x : α, spatial x * finiteUniformAverageComplementLinearMap f x := by
  classical
  have hn : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  rw [finiteUniformAverageProjectorLinearMap_apply]
  simp_rw [finiteUniformNormalizedAdditiveFirstVariationKernel_apply_complement
    spatial crossingMean normalizationDerivative f]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]

/-- Pairwise output difference after the disconnected composition
`T₁ P₀ T₁ Q`. -/
theorem finiteUniformNormalizedAdditiveFirstVariation_groundMixing_sub
    {α : Type} [Fintype α] [Nonempty α]
    (spatial : α → ℝ)
    (crossingMean normalizationDerivative : ℝ)
    (f : FiniteBoundaryHilbert α)
    (y y' : α) :
    let K := finiteUniformNormalizedAdditiveFirstVariationKernel
      spatial crossingMean normalizationDerivative
    let q := finiteUniformAverageComplementLinearMap f
    let g := finiteKernelOperator K
      (finiteUniformAverageProjectorLinearMap (finiteKernelOperator K q))
    g y - g y' =
      (Fintype.card α : ℝ)⁻¹ * (1 / 4 : ℝ) *
        (∑ x : α, spatial x * q x) * (spatial y - spatial y') := by
  classical
  dsimp
  have hn : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  let c : ℝ :=
    -(Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) *
      ∑ x : α, spatial x * finiteUniformAverageComplementLinearMap f x
  have hP : ∀ x : α,
      finiteUniformAverageProjectorLinearMap
          (finiteKernelOperator
            (finiteUniformNormalizedAdditiveFirstVariationKernel
              spatial crossingMean normalizationDerivative)
            (finiteUniformAverageComplementLinearMap f)) x = c := by
    intro x
    dsimp [c]
    exact
      finiteUniformAverageProjectorLinearMap_comp_additiveFirstVariation_apply_complement
        spatial crossingMean normalizationDerivative f x
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ x : α, (
      finiteUniformNormalizedAdditiveFirstVariationKernel
          spatial crossingMean normalizationDerivative x y *
          finiteUniformAverageProjectorLinearMap
            (finiteKernelOperator
              (finiteUniformNormalizedAdditiveFirstVariationKernel
                spatial crossingMean normalizationDerivative)
              (finiteUniformAverageComplementLinearMap f)) x -
        finiteUniformNormalizedAdditiveFirstVariationKernel
          spatial crossingMean normalizationDerivative x y' *
          finiteUniformAverageProjectorLinearMap
            (finiteKernelOperator
              (finiteUniformNormalizedAdditiveFirstVariationKernel
                spatial crossingMean normalizationDerivative)
              (finiteUniformAverageComplementLinearMap f)) x)) =
      ∑ _x : α,
        (-(Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) *
          (spatial y - spatial y')) * c := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [hP x]
        unfold finiteUniformNormalizedAdditiveFirstVariationKernel
        ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [c]
      field_simp [hn]
      ring

/-- Pairwise output difference of the normalized spatial rank-one kernel on a
complemented input. -/
theorem finiteUniformNormalizedSpatialRankOneKernel_apply_complement_sub
    {α : Type} [Fintype α] [Nonempty α]
    (spatial : α → ℝ)
    (f : FiniteBoundaryHilbert α)
    (y y' : α) :
    finiteKernelOperator
        (finiteUniformNormalizedSpatialRankOneKernel spatial)
        (finiteUniformAverageComplementLinearMap f) y -
      finiteKernelOperator
        (finiteUniformNormalizedSpatialRankOneKernel spatial)
        (finiteUniformAverageComplementLinearMap f) y' =
      (Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) *
        (∑ x : α,
          spatial x * finiteUniformAverageComplementLinearMap f x) *
        (spatial y - spatial y') := by
  classical
  rw [finiteKernelOperator_apply, finiteKernelOperator_apply,
    ← Finset.sum_sub_distrib]
  unfold finiteUniformNormalizedSpatialRankOneKernel
  calc
    (∑ x : α, (
      (Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) * spatial x * spatial y *
          finiteUniformAverageComplementLinearMap f x -
        (Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ) * spatial x * spatial y' *
          finiteUniformAverageComplementLinearMap f x)) =
      ∑ x : α,
        ((Fintype.card α : ℝ)⁻¹ * (1 / 2 : ℝ)) *
          (spatial x * finiteUniformAverageComplementLinearMap f x) *
          (spatial y - spatial y') := by
        apply Finset.sum_congr rfl
        intro x _hx
        ring
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

/-- Exact generic disconnected-mixing cancellation:

`2 Q T₁ P₀ T₁ Q = Q R_spatial Q`,

where `P₀` is uniform averaging, `Q = I - P₀`, `T₁` is any scalar-normalized
additive first-variation kernel at the exact beta-zero normalization value
`1 / |α|`, and `R_spatial(x,y) = |α|⁻¹ (1/2) S(x)S(y)`.

The arbitrary normalization derivative and the boundary-independent crossing
mean drop out identically. -/
theorem finiteUniformNormalizedAdditiveFirstVariation_groundMixing_double_eq_spatialRankOne
    {α : Type} [Fintype α] [Nonempty α]
    (spatial : α → ℝ)
    (crossingMean normalizationDerivative : ℝ) :
    let T₁ :=
      (finiteKernelOperator
        (finiteUniformNormalizedAdditiveFirstVariationKernel
          spatial crossingMean normalizationDerivative)).toLinearMap
    let P₀ :=
      (finiteUniformAverageProjectorLinearMap :
        FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α)
    let Q :=
      (finiteUniformAverageComplementLinearMap :
        FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α)
    let R :=
      (finiteKernelOperator
        (finiteUniformNormalizedSpatialRankOneKernel spatial)).toLinearMap
    Q.comp (T₁.comp (P₀.comp (T₁.comp Q))) +
        Q.comp (T₁.comp (P₀.comp (T₁.comp Q))) =
      Q.comp (R.comp Q) := by
  classical
  dsimp
  apply LinearMap.ext
  intro f
  let K := finiteUniformNormalizedAdditiveFirstVariationKernel
    spatial crossingMean normalizationDerivative
  let q : FiniteBoundaryHilbert α := finiteUniformAverageComplementLinearMap f
  let g : FiniteBoundaryHilbert α :=
    finiteKernelOperator K
      (finiteUniformAverageProjectorLinearMap (finiteKernelOperator K q))
  let r : FiniteBoundaryHilbert α :=
    finiteKernelOperator (finiteUniformNormalizedSpatialRankOneKernel spatial) q
  have hpair : ∀ y y' : α, (g + g) y - (g + g) y' = r y - r y' := by
    intro y y'
    have hm :=
      finiteUniformNormalizedAdditiveFirstVariation_groundMixing_sub
        spatial crossingMean normalizationDerivative f y y'
    have hr :=
      finiteUniformNormalizedSpatialRankOneKernel_apply_complement_sub
        spatial f y y'
    dsimp [K, q, g, r] at hm hr ⊢
    linear_combination 2 * hm - hr
  have hQ :=
    finiteUniformAverageComplementLinearMap_eq_of_pairwise_sub_eq
      (g + g) r hpair
  rw [map_add] at hQ
  change
    finiteUniformAverageComplementLinearMap g +
        finiteUniformAverageComplementLinearMap g =
      finiteUniformAverageComplementLinearMap r
  exact hQ

end

end MathlibAnalytic
end MGAP4D
