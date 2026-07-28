import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertSymmetricContractionSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- At every even natural time, the temporal OS quadratic form is the squared
norm of the half-time translate. -/
theorem inner_hilbertShiftSemigroup_add_self_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.Hilbert) :
    inner ℝ (D.hilbertShiftSemigroup (n + n) x) x =
      inner ℝ (D.hilbertShiftSemigroup n x)
        (D.hilbertShiftSemigroup n x) := by
  rw [D.hilbertShiftSemigroup_add]
  exact D.inner_hilbertShiftSemigroup_left_eq_right n
    (D.hilbertShiftSemigroup n x) x

/-- Every even-time member of the temporal OS semigroup has nonnegative
quadratic form. -/
theorem inner_hilbertShiftSemigroup_add_self_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.Hilbert) :
    0 ≤ inner ℝ (D.hilbertShiftSemigroup (n + n) x) x := by
  rw [D.inner_hilbertShiftSemigroup_add_self_eq]
  exact inner_self_nonneg ℝ (D.hilbertShiftSemigroup n x)

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
