import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossRatioInfluenceTransform
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite family of nonnegative multiplicative residuals linearizes after
the canonical cross-ratio influence transform.  No cardinality factor is
introduced: each logarithmic residual `log (1 + x_i)` contributes at most
`x_i`, and the inequalities are summed directly. -/
theorem finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_le
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + x i))) ≤
      ∑ i ∈ s, x i := by
  apply Finset.sum_le_sum
  intro i hi
  exact
    finitePositiveWeightCrossRatioInfluenceTransform_log_one_add_le
      (x i) (hx i hi)

/-- Target-dependent nonnegative multipliers may be absorbed into the residual
before linearization.  This is the form needed when each remote target has its
own response-to-cross-ratio prefactor. -/
theorem finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_mul_le
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (multiplier error : ι → ℝ)
    (hMultiplier : ∀ i ∈ s, 0 ≤ multiplier i)
    (hError : ∀ i ∈ s, 0 ≤ error i) :
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + multiplier i * error i))) ≤
      ∑ i ∈ s, multiplier i * error i := by
  apply Finset.sum_le_sum
  intro i hi
  exact
    finitePositiveWeightCrossRatioInfluenceTransform_log_one_add_le
      (multiplier i * error i)
      (mul_nonneg (hMultiplier i hi) (hError i hi))

/-- For one common nonnegative multiplier, the preceding finite-family bound
factors exactly as `multiplier * sum error`. -/
theorem finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_const_mul_le
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (multiplier : ℝ)
    (error : ι → ℝ)
    (hMultiplier : 0 ≤ multiplier)
    (hError : ∀ i ∈ s, 0 ≤ error i) :
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + multiplier * error i))) ≤
      multiplier * ∑ i ∈ s, error i := by
  calc
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + multiplier * error i))) ≤
      ∑ i ∈ s, multiplier * error i := by
        exact
          finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_mul_le
            s (fun _ => multiplier) error
            (by
              intro i hi
              exact hMultiplier)
            hError
    _ = multiplier * ∑ i ∈ s, error i := by
      rw [Finset.mul_sum]

/-- If target-dependent multipliers are uniformly bounded by one nonnegative
constant, the total transformed residual is controlled by that constant times
the unweighted residual sum.  This is the finite-family form compatible with
target-indexed worst-case response data. -/
theorem finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_mul_le_const_mul_sum
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (multiplier error : ι → ℝ)
    (bound : ℝ)
    (hMultiplier : ∀ i ∈ s, 0 ≤ multiplier i)
    (hMultiplierLe : ∀ i ∈ s, multiplier i ≤ bound)
    (hError : ∀ i ∈ s, 0 ≤ error i) :
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + multiplier i * error i))) ≤
      bound * ∑ i ∈ s, error i := by
  calc
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + multiplier i * error i))) ≤
      ∑ i ∈ s, multiplier i * error i :=
        finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_mul_le
          s multiplier error hMultiplier hError
    _ ≤ ∑ i ∈ s, bound * error i := by
      apply Finset.sum_le_sum
      intro i hi
      exact
        mul_le_mul_of_nonneg_right
          (hMultiplierLe i hi)
          (hError i hi)
    _ = bound * ∑ i ∈ s, error i := by
      rw [Finset.mul_sum]

/-- A pre-existing bound on the source-summed response residual can therefore
be transported directly to the source-summed cross-ratio influence.  This
statement isolates the normalization algebra from any model-specific proof of
the residual bound itself. -/
theorem finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_const_mul_le_of_sum_le
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (multiplier residualBound : ℝ)
    (error : ι → ℝ)
    (hMultiplier : 0 ≤ multiplier)
    (hError : ∀ i ∈ s, 0 ≤ error i)
    (hErrorSum : (∑ i ∈ s, error i) ≤ residualBound) :
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + multiplier * error i))) ≤
      multiplier * residualBound := by
  calc
    (∑ i ∈ s,
      finitePositiveWeightCrossRatioInfluenceTransform
        (Real.log (1 + multiplier * error i))) ≤
      multiplier * ∑ i ∈ s, error i :=
        finitePositiveWeightCrossRatioInfluenceTransform_sum_log_one_add_const_mul_le
          s multiplier error hMultiplier hError
    _ ≤ multiplier * residualBound :=
      mul_le_mul_of_nonneg_left hErrorSum hMultiplier

end

end MathlibAnalytic
end MGAP4D
