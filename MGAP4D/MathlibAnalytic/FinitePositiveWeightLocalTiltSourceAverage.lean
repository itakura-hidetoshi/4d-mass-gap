import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltConditional
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
  exact le_rfl

end

end MathlibAnalytic
end MGAP4D
