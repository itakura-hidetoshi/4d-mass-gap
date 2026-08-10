import MGAP4D.MathlibAnalytic.UniformQuadraticCoercivityLimitPosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Matrix

noncomputable section

universe u v

/-- A finite linearly independent family in a real normed space has a strictly
positive Euclidean lower-frame bound.

The proof is entirely finite-dimensional: the coefficient synthesis map on
`EuclideanSpace ℝ ι` is injective by linear independence, hence Mathlib's
`LinearMap.injective_iff_antilipschitz` supplies a quantitative lower bound. -/
theorem exists_pos_sum_sq_le_norm_sq_of_linearIndependent
    {ι : Type u} [Fintype ι]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ι → E)
    (hv : LinearIndependent ℝ v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ι → ℝ,
      δ * (∑ i, x i ^ 2) ≤ ‖∑ i, x i • v i‖ ^ 2 := by
  classical
  let S : EuclideanSpace ℝ ι →ₗ[ℝ] E :=
    (Fintype.linearCombination ℝ v).comp
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap
  have hS : Function.Injective S :=
    hv.fintypeLinearCombination_injective.comp
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective
  rcases (LinearMap.injective_iff_antilipschitz S).mp hS with
    ⟨K, hK, hAnti⟩
  have hKreal : 0 < (K : ℝ) := by
    exact_mod_cast hK
  have hKinv : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hKreal
  refine ⟨((K : ℝ)⁻¹ ^ 2), sq_pos_of_pos hKinv, ?_⟩
  intro x
  let y : EuclideanSpace ℝ ι := WithLp.toLp 2 x
  have hbound :
      (K : ℝ)⁻¹ * ‖y‖ ≤ ‖S y‖ := by
    simpa using hAnti.mul_le_dist y 0
  have hsq :
      (((K : ℝ)⁻¹ * ‖y‖) ^ 2) ≤ ‖S y‖ ^ 2 := by
    have hprod :
        0 ≤
          (‖S y‖ - (K : ℝ)⁻¹ * ‖y‖) *
            (‖S y‖ + (K : ℝ)⁻¹ * ‖y‖) :=
      mul_nonneg
        (sub_nonneg.mpr hbound)
        (add_nonneg (norm_nonneg _) (mul_nonneg hKinv.le (norm_nonneg _)))
    nlinarith
  have hynorm : ‖y‖ ^ 2 = ∑ i, x i ^ 2 := by
    simpa [y] using EuclideanSpace.real_norm_sq_eq y
  have hSy : S y = ∑ i, x i • v i := by
    simp [S, y, Fintype.linearCombination_apply]
  calc
    ((K : ℝ)⁻¹ ^ 2) * (∑ i, x i ^ 2) =
        (((K : ℝ)⁻¹ * ‖y‖) ^ 2) := by
      rw [← hynorm]
      ring
    _ ≤ ‖S y‖ ^ 2 := hsq
    _ = ‖∑ i, x i • v i‖ ^ 2 := by rw [hSy]

/-- Strict positivity survives a quadratic-form limit when the same positive
coercivity constant holds eventually along the approximating sequence.

This is the tail-uniform form needed for local/projective Wilson families:
finitely many initial volumes may be discarded. -/
theorem matrix_posDef_of_eventually_uniform_quadratic_coercivity_tendsto
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℝ)
    (A_limit : Matrix ι ι ℝ)
    (hHermitian : Matrix.IsHermitian A_limit)
    (δ : ℝ) (hδ : 0 < δ)
    (hTendsto : ∀ x : ι → ℝ,
      Tendsto
        (fun n : ℕ => dotProduct (star x) (Matrix.mulVec (A n) x))
        atTop
        (nhds (dotProduct (star x) (Matrix.mulVec A_limit x))))
    (hCoercive : ∀ᶠ n in atTop, ∀ x : ι → ℝ,
      δ * (∑ i, x i ^ 2) ≤
        dotProduct (star x) (Matrix.mulVec (A n) x)) :
    A_limit.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian
  intro x hx
  have henergy : 0 < δ * (∑ i, x i ^ 2) :=
    mul_pos hδ (finset_sum_sq_pos_of_ne_zero x hx)
  have hlower : ∀ᶠ n in atTop,
      δ * (∑ i, x i ^ 2) ≤
        dotProduct (star x) (Matrix.mulVec (A n) x) :=
    hCoercive.mono fun n hn => hn x
  exact henergy.trans_le (ge_of_tendsto (hTendsto x) hlower)

end

end MathlibAnalytic
end MGAP4D
