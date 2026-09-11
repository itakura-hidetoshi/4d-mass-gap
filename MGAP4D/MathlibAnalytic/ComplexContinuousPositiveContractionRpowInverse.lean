import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionRpow

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace ComplexContinuousPositiveContraction

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- If `S` is an explicit two-sided inverse of a positive complex operator `T`,
then the unital CFC power at exponent `-1` is exactly `S`. -/
theorem rpow_neg_one_eq_explicitInverse
    (T S : H →L[ℂ] H)
    (hpositive : T.IsPositive)
    (hTS : T * S = 1)
    (hST : S * T = 1) :
    rpow T (-1) = S := by
  let u : (H →L[ℂ] H)ˣ :=
    { val := T
      inv := S
      val_inv := hTS
      inv_val := hST }
  have hnonneg : (0 : H →L[ℂ] H) ≤ T :=
    (ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive
  unfold rpow
  simpa [u] using
    (CFC.rpow_neg_one_eq_inv u (by simpa [u] using hnonneg))

/-- Negative real powers of a positive operator with explicit inverse are the
corresponding positive powers of that inverse. -/
theorem rpow_neg_eq_explicitInverse_rpow
    (T S : H →L[ℂ] H)
    (x : ℝ)
    (hpositive : T.IsPositive)
    (hTS : T * S = 1)
    (hST : S * T = 1) :
    rpow T (-x) = rpow S x := by
  let u : (H →L[ℂ] H)ˣ :=
    { val := T
      inv := S
      val_inv := hTS
      inv_val := hST }
  have hnonneg : (0 : H →L[ℂ] H) ≤ T :=
    (ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive
  unfold rpow
  simpa [u] using CFC.rpow_neg u x (by simpa [u] using hnonneg)

/-- For a positive invertible operator, a real power multiplied by the opposite
power is the identity. -/
theorem rpow_mul_rpow_neg_of_isUnit
    (T : H →L[ℂ] H)
    (x : ℝ)
    (hpositive : T.IsPositive)
    (hunit : IsUnit T) :
    rpow T x * rpow T (-x) = 1 := by
  rw [← rpow_add_of_isUnit T x (-x) hunit, add_neg_cancel,
    rpow_zero T hpositive]

/-- For a positive invertible operator, the opposite real power multiplied by
the original power is the identity. -/
theorem rpow_neg_mul_rpow_of_isUnit
    (T : H →L[ℂ] H)
    (x : ℝ)
    (hpositive : T.IsPositive)
    (hunit : IsUnit T) :
    rpow T (-x) * rpow T x = 1 := by
  rw [← rpow_add_of_isUnit T (-x) x hunit, neg_add_cancel,
    rpow_zero T hpositive]

end ComplexContinuousPositiveContraction

end

end MathlibAnalytic
end MGAP4D
