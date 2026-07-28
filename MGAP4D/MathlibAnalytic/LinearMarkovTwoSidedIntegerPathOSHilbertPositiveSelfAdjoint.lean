import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertOddTimePositive
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Every natural-time member of the temporal OS semigroup has nonnegative
quadratic form once the stationary one-step transition quadratic form is
nonnegative. -/
theorem inner_hilbertShiftSemigroup_self_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    (x : D.Hilbert) :
    0 ≤ inner ℝ (D.hilbertShiftSemigroup n x) x := by
  refine Nat.evenOddRec ?_ (fun k _hk => ?_) (fun k _hk => ?_) n
  · simpa using D.inner_hilbertShiftSemigroup_add_self_nonneg 0 x
  · simpa [two_mul] using D.inner_hilbertShiftSemigroup_add_self_nonneg k x
  · simpa [two_mul] using
      D.inner_hilbertShiftSemigroup_add_self_add_one_nonneg hquad k x

/-- Every natural-time member of the temporal OS semigroup is symmetric as a
continuous linear operator. -/
theorem hilbertShiftSemigroup_isSymmetric
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    (D.hilbertShiftSemigroup n : D.Hilbert →ₗ[ℝ] D.Hilbert).IsSymmetric := by
  intro x y
  exact D.inner_hilbertShiftSemigroup_left_eq_right n x y

/-- Every natural-time temporal OS operator is positive in Mathlib's bundled
continuous-linear-map sense. -/
theorem hilbertShiftSemigroup_isPositive
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    (D.hilbertShiftSemigroup n).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  exact ⟨D.hilbertShiftSemigroup_isSymmetric n,
    D.inner_hilbertShiftSemigroup_self_nonneg hquad n⟩

/-- Every natural-time temporal OS operator is nonnegative in Mathlib's Loewner
order on continuous linear endomorphisms. -/
theorem hilbertShiftSemigroup_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    0 ≤ D.hilbertShiftSemigroup n :=
  (ContinuousLinearMap.nonneg_iff_isPositive
    (D.hilbertShiftSemigroup n)).2
      (D.hilbertShiftSemigroup_isPositive hquad n)

/-- Every natural-time temporal OS operator is self-adjoint. -/
theorem hilbertShiftSemigroup_isSelfAdjoint
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ) :
    IsSelfAdjoint (D.hilbertShiftSemigroup n) :=
  (D.hilbertShiftSemigroup_isPositive hquad n).isSelfAdjoint

/-- The Hilbert-space adjoint of every natural-time temporal OS operator is the
operator itself. -/
theorem hilbertShiftSemigroup_adjoint_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ) :
    ContinuousLinearMap.adjoint (D.hilbertShiftSemigroup n) =
      D.hilbertShiftSemigroup n :=
  (D.hilbertShiftSemigroup_isSymmetric n).clm_adjoint_eq

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
