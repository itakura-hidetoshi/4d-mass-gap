import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertPositiveSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Every natural-time temporal OS quadratic form is bounded above by the
ambient squared norm. -/
theorem inner_hilbertShiftSemigroup_self_le
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.Hilbert) :
    inner ℝ (D.hilbertShiftSemigroup n x) x ≤ inner ℝ x x := by
  calc
    inner ℝ (D.hilbertShiftSemigroup n x) x ≤
        ‖D.hilbertShiftSemigroup n x‖ * ‖x‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (D.norm_hilbertShiftSemigroup_le n x) (norm_nonneg x)
    _ = ‖x‖ ^ 2 := by ring
    _ = inner ℝ x x := by
      rw [real_inner_self_eq_norm_sq]

/-- The complement of every natural-time temporal OS operator is positive. -/
theorem one_sub_hilbertShiftSemigroup_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    ((1 : D.Hilbert →L[ℝ] D.Hilbert) -
      D.hilbertShiftSemigroup n).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    change inner ℝ (x - D.hilbertShiftSemigroup n x) y =
      inner ℝ x (y - D.hilbertShiftSemigroup n y)
    rw [inner_sub_left, inner_sub_right,
      D.inner_hilbertShiftSemigroup_left_eq_right]
  · intro x
    change 0 ≤ inner ℝ (x - D.hilbertShiftSemigroup n x) x
    rw [inner_sub_left]
    exact sub_nonneg.mpr (D.inner_hilbertShiftSemigroup_self_le n x)

/-- Every natural-time temporal OS operator is at most the identity in
Mathlib's Loewner order. -/
theorem hilbertShiftSemigroup_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    D.hilbertShiftSemigroup n ≤ 1 :=
  (ContinuousLinearMap.le_def _ _).2
    (D.one_sub_hilbertShiftSemigroup_isPositive n)

/-- Every natural-time temporal OS operator belongs to the Loewner interval
`[0, I]`. -/
theorem hilbertShiftSemigroup_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    D.hilbertShiftSemigroup n ∈
      Set.Icc (0 : D.Hilbert →L[ℝ] D.Hilbert) 1 :=
  ⟨D.hilbertShiftSemigroup_nonneg hquad n,
    D.hilbertShiftSemigroup_le_one n⟩

/-- The Rayleigh quotient of every natural-time temporal OS operator is
nonnegative. -/
theorem hilbertShiftSemigroup_rayleighQuotient_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    (x : D.Hilbert) :
    0 ≤ (D.hilbertShiftSemigroup n).rayleighQuotient x := by
  change 0 ≤ inner ℝ (D.hilbertShiftSemigroup n x) x / ‖x‖ ^ 2
  exact div_nonneg
    (D.inner_hilbertShiftSemigroup_self_nonneg hquad n x)
    (sq_nonneg ‖x‖)

/-- The Rayleigh quotient of every natural-time temporal OS operator is at
most one. -/
theorem hilbertShiftSemigroup_rayleighQuotient_le_one
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.Hilbert) :
    (D.hilbertShiftSemigroup n).rayleighQuotient x ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · change inner ℝ (D.hilbertShiftSemigroup n x) x / ‖x‖ ^ 2 ≤ 1
    rw [div_le_iff₀ (pow_pos (norm_pos_iff.mpr hx) 2)]
    simpa using D.inner_hilbertShiftSemigroup_self_le n x

/-- Every natural-time temporal OS Rayleigh quotient belongs to `[0, 1]`. -/
theorem hilbertShiftSemigroup_rayleighQuotient_mem_Icc
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    (x : D.Hilbert) :
    (D.hilbertShiftSemigroup n).rayleighQuotient x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨D.hilbertShiftSemigroup_rayleighQuotient_nonneg hquad n x,
    D.hilbertShiftSemigroup_rayleighQuotient_le_one n x⟩

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
