import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

namespace ComplexContinuousSymmetricContraction

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The real part of the quadratic form of a complex contraction is bounded by
that of the identity. -/
theorem re_inner_apply_self_le
    (T : H →L[ℂ] H)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖)
    (x : H) :
    (inner ℂ (T x) x).re ≤ (inner ℂ x x).re := by
  calc
    (inner ℂ (T x) x).re ≤ ‖T x‖ * ‖x‖ :=
      re_inner_le_norm (𝕜 := ℂ) (T x) x
    _ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right (hcontract x) (norm_nonneg x)
    _ = ‖x‖ ^ 2 := by ring
    _ = (inner ℂ x x).re := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
      simp [pow_two]

/-- The complement of a symmetric complex contraction is positive. -/
theorem one_sub_isPositive
    (T : H →L[ℂ] H)
    (hsym : T.IsSymmetric)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖) :
    ((1 : H →L[ℂ] H) - T).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  constructor
  · intro x y
    change inner ℂ (x - T x) y = inner ℂ x (y - T y)
    rw [inner_sub_left, inner_sub_right]
    exact congrArg (fun z : ℂ => inner ℂ x y - z) (hsym x y)
  · intro x
    change 0 ≤ (inner ℂ (x - T x) x).re
    rw [inner_sub_left]
    change 0 ≤ (inner ℂ x x).re - (inner ℂ (T x) x).re
    exact sub_nonneg.mpr (re_inner_apply_self_le T hcontract x)

/-- A symmetric complex contraction is at most the identity in Mathlib's
Loewner order. -/
theorem le_one
    (T : H →L[ℂ] H)
    (hsym : T.IsSymmetric)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖) :
    T ≤ 1 :=
  (ContinuousLinearMap.le_def T 1).2
    (one_sub_isPositive T hsym hcontract)

/-- A positive symmetric complex contraction belongs to the Loewner interval
`[0, I]`. -/
theorem mem_Icc
    (T : H →L[ℂ] H)
    (hpositive : T.IsPositive)
    (hsym : T.IsSymmetric)
    (hcontract : ∀ x, ‖T x‖ ≤ ‖x‖) :
    T ∈ Set.Icc (0 : H →L[ℂ] H) 1 :=
  ⟨(ContinuousLinearMap.nonneg_iff_isPositive T).2 hpositive,
    le_one T hsym hcontract⟩

end ComplexContinuousSymmetricContraction

end

end MathlibAnalytic
end MGAP4D
