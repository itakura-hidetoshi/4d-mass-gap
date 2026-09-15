import MGAP4D.MathlibAnalytic.FinitePositiveWeightNonstrictStationaryResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The explicit source vector of a bounded local multiplicative tilt has
volume-normalized total bounded by the same likelihood-ratio constant.  This
is the generic source-average certificate needed by the stationary C5 bridge. -/
theorem finitePositiveWeightLocalTiltConditionalSourceBound_total_le_card_mul
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (support : Finset ι)
    (lower upper : ℝ)
    (hLower : 0 < lower)
    (hUpper : 0 < upper)
    (hLowerUpper : lower ≤ upper) :
    finiteProductVariationTotal
        (finitePositiveWeightLocalTiltConditionalSourceBound
          support lower upper) ≤
      (Fintype.card ι : ℝ) *
        (2 * (1 - (upper / lower)⁻¹)) := by
  have hRatioOne : 1 ≤ upper / lower :=
    (le_div_iff₀ hLower).2 (by simpa using hLowerUpper)
  have hRatioPos : 0 < upper / lower := div_pos hUpper hLower
  have hInvLeOne : (upper / lower)⁻¹ ≤ 1 :=
    (inv_le_one₀ hRatioPos).2 hRatioOne
  have hConstNonneg :
      0 ≤ 2 * (1 - (upper / lower)⁻¹) := by
    nlinarith
  unfold finiteProductVariationTotal
  calc
    (∑ target : ι,
      finitePositiveWeightLocalTiltConditionalSourceBound
        support lower upper target) ≤
      ∑ _target : ι, (2 * (1 - (upper / lower)⁻¹)) := by
        apply Finset.sum_le_sum
        intro target _htarget
        unfold finitePositiveWeightLocalTiltConditionalSourceBound
        split
        · exact le_rfl
        · exact hConstNonneg
    _ = (Fintype.card ι : ℝ) *
        (2 * (1 - (upper / lower)⁻¹)) := by
      simp

end

end MathlibAnalytic
end MGAP4D
