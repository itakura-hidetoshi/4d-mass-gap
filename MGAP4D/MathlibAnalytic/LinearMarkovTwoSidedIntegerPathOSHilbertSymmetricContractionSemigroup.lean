import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertShiftSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The time-one member of the discrete temporal OS semigroup is the completed
one-step shift. -/
@[simp] theorem hilbertShiftSemigroup_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.hilbertShiftSemigroup 1 = D.hilbertShiftContinuousLinearMap := by
  ext x
  rfl

/-- Any two members of the discrete temporal OS semigroup commute. -/
theorem hilbertShiftSemigroup_comp_comm
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (m n : ℕ) :
    (D.hilbertShiftSemigroup m).comp (D.hilbertShiftSemigroup n) =
      (D.hilbertShiftSemigroup n).comp (D.hilbertShiftSemigroup m) := by
  rw [← D.hilbertShiftSemigroup_add, Nat.add_comm,
    D.hilbertShiftSemigroup_add]

/-- Pointwise commutation of any two members of the discrete temporal OS
semigroup. -/
theorem hilbertShiftSemigroup_apply_comm
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (m n : ℕ)
    (x : D.Hilbert) :
    D.hilbertShiftSemigroup m (D.hilbertShiftSemigroup n x) =
      D.hilbertShiftSemigroup n (D.hilbertShiftSemigroup m x) := by
  have h := congrArg
    (fun T : D.Hilbert →L[ℝ] D.Hilbert => T x)
    (D.hilbertShiftSemigroup_comp_comm m n)
  exact h

/-- Every discrete-time member of the completed temporal OS semigroup is
symmetric on the real Hilbert space. -/
theorem inner_hilbertShiftSemigroup_left_eq_right
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x y : D.Hilbert) :
    inner ℝ (D.hilbertShiftSemigroup n x) y =
      inner ℝ x (D.hilbertShiftSemigroup n y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      rw [D.hilbertShiftSemigroup_succ_apply,
        D.inner_hilbertShiftContinuousLinearMap_left_eq_right,
        ih]
      rw [D.hilbertShiftSemigroup_apply_comm n 1]
      rfl

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
