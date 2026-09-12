import MGAP4D.MathlibAnalytic.FinitePositiveWeightCanonicalVariationDefiniteness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Proof-relevant coordinate influence matrix for a parallel finite-product
linear operator.  The first matrix index is the output variation coordinate;
the second is the input variation coordinate.  A strict column-sum bound is
therefore exactly what contracts total canonical variation. -/
structure FiniteProductParallelVariationMatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ)) where
  influence : ι → ι → ℝ
  influence_nonneg :
    ∀ target source : ι, 0 ≤ influence target source
  canonicalVariation_le :
    ∀ (f : (ι → G) → ℝ) (target : ι),
      finiteProductCanonicalVariation (T f) target ≤
        ∑ source : ι,
          influence target source *
            finiteProductCanonicalVariation f source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  columnSum_le_coefficient :
    ∀ source : ι,
      (∑ target : ι, influence target source) ≤ coefficient
  coefficient_lt_one : coefficient < 1

/-- A strict column-sum influence bound contracts total canonical variation for
one application of the parallel operator. -/
theorem finiteProductParallel_canonicalTotalVariation_le_coefficient_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FiniteProductParallelVariationMatrixData T)
    (f : (ι → G) → ℝ) :
    finiteProductCanonicalTotalVariation (T f) ≤
      D.coefficient * finiteProductCanonicalTotalVariation f := by
  classical
  unfold finiteProductCanonicalTotalVariation
  calc
    (∑ target : ι, finiteProductCanonicalVariation (T f) target) ≤
        ∑ target : ι,
          ∑ source : ι,
            D.influence target source *
              finiteProductCanonicalVariation f source := by
      apply Finset.sum_le_sum
      intro target _htarget
      exact D.canonicalVariation_le f target
    _ = ∑ source : ι,
        ∑ target : ι,
          D.influence target source *
            finiteProductCanonicalVariation f source := by
      rw [Finset.sum_comm]
    _ = ∑ source : ι,
        (∑ target : ι, D.influence target source) *
          finiteProductCanonicalVariation f source := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_mul]
    _ ≤ ∑ source : ι,
        D.coefficient * finiteProductCanonicalVariation f source := by
      apply Finset.sum_le_sum
      intro source _hsource
      exact mul_le_mul_of_nonneg_right
        (D.columnSum_le_coefficient source)
        (finiteProductCanonicalVariation_nonneg f source)
    _ = D.coefficient *
        ∑ source : ι, finiteProductCanonicalVariation f source := by
      rw [Finset.mul_sum]

/-- Every eigenobservable with nonzero total coordinate variation has
parallel eigenvalue bounded in modulus by the influence column norm. -/
theorem finiteProductParallel_eigenvalue_abs_le_coefficient
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FiniteProductParallelVariationMatrixData T)
    (f : (ι → G) → ℝ)
    (eigenvalue : ℝ)
    (hEigen : T f = eigenvalue • f)
    (hVariation : finiteProductCanonicalTotalVariation f ≠ 0) :
    |eigenvalue| ≤ D.coefficient := by
  have hContract :=
    finiteProductParallel_canonicalTotalVariation_le_coefficient_mul
      T D f
  rw [hEigen, finiteProductCanonicalTotalVariation_smul] at hContract
  have hVariationPos : 0 < finiteProductCanonicalTotalVariation f :=
    lt_of_le_of_ne
      (finiteProductCanonicalTotalVariation_nonneg f)
      (Ne.symm hVariation)
  nlinarith

/-- On a strictly positive weighted centered sector, every nonzero parallel
eigenobservable has eigenvalue bounded by the same coefficient. -/
theorem finitePositiveWeight_centered_parallel_eigenvalue_abs_le_coefficient
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FiniteProductParallelVariationMatrixData T)
    (f : (ι → G) → ℝ)
    (eigenvalue : ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0)
    (hNonzero : f ≠ 0)
    (hEigen : T f = eigenvalue • f) :
    |eigenvalue| ≤ D.coefficient := by
  exact finiteProductParallel_eigenvalue_abs_le_coefficient
    T D f eigenvalue hEigen
    (finitePositiveWeight_centered_canonicalTotalVariation_ne_zero
      weight hweight f hCenter hNonzero)

/-- In particular, every nonzero centered parallel eigenobservable has
real eigenvalue strictly below one. -/
theorem finitePositiveWeight_centered_parallel_eigenvalue_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (T : ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ))
    (D : FiniteProductParallelVariationMatrixData T)
    (f : (ι → G) → ℝ)
    (eigenvalue : ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0)
    (hNonzero : f ≠ 0)
    (hEigen : T f = eigenvalue • f) :
    eigenvalue < 1 := by
  have hAbs :=
    finitePositiveWeight_centered_parallel_eigenvalue_abs_le_coefficient
      weight hweight T D f eigenvalue hCenter hNonzero hEigen
  exact lt_of_le_of_lt
    (le_trans (le_abs_self eigenvalue) hAbs)
    D.coefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
