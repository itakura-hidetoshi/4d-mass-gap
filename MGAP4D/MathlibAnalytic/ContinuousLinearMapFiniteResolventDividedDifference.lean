import MGAP4D.MathlibAnalytic.ContinuousLinearMapResolventDividedDifference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProducts
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Recursive divided difference of a finite list of bounded operator values.
The recursion removes the second entry in one branch and the first entry in the
other, so every recursive call has strictly shorter length. -/
def finiteResolventDividedDifference
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E) :
    List α → E →L[ℝ] E
  | [] => 1
  | [a] => A a
  | a :: b :: tail =>
      (parameter a - parameter b)⁻¹ •
        (finiteResolventDividedDifference parameter A (a :: tail) -
          finiteResolventDividedDifference parameter A (b :: tail))
termination_by s => s.length

@[simp] theorem finiteResolventDividedDifference_nil
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E) :
    finiteResolventDividedDifference parameter A [] = 1 := rfl

@[simp] theorem finiteResolventDividedDifference_singleton
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E)
    (a : α) :
    finiteResolventDividedDifference parameter A [a] = A a := rfl

@[simp] theorem finiteResolventDividedDifference_cons_cons
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E)
    (a b : α)
    (tail : List α) :
    finiteResolventDividedDifference parameter A (a :: b :: tail) =
      (parameter a - parameter b)⁻¹ •
        (finiteResolventDividedDifference parameter A (a :: tail) -
          finiteResolventDividedDifference parameter A (b :: tail)) := rfl

/-- If a bounded operator family satisfies the real resolvent identity, then
its recursive divided difference over every parameter-distinct finite list is
exactly the ordered product of the corresponding resolvents. -/
theorem finiteResolventDividedDifference_eq_orderedProduct_of_pairwise
    (parameter : α → ℝ)
    (A : α → E →L[ℝ] E)
    (hIdentity : ∀ a b,
      parameter a ≠ parameter b →
        A a - A b =
          (parameter a - parameter b) • (A a * A b))
    (s : List α)
    (hPairwise : s.Pairwise fun a b => parameter a ≠ parameter b) :
    finiteResolventDividedDifference parameter A s = orderedProduct A s := by
  cases s with
  | nil => rfl
  | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail =>
          rw [finiteResolventDividedDifference_cons_cons]
          rcases List.pairwise_cons.mp hPairwise with ⟨ha, hBTail⟩
          rcases List.pairwise_cons.mp hBTail with ⟨hb, hTail⟩
          have hab : parameter a ≠ parameter b :=
            ha b (by simp)
          have hATail :
              (a :: tail).Pairwise fun x y => parameter x ≠ parameter y := by
            apply List.pairwise_cons.mpr
            constructor
            · intro x hx
              exact ha x (by simp [hx])
            · exact hTail
          have ihA :=
            finiteResolventDividedDifference_eq_orderedProduct_of_pairwise
              parameter A hIdentity (a :: tail) hATail
          have ihB :=
            finiteResolventDividedDifference_eq_orderedProduct_of_pairwise
              parameter A hIdentity (b :: tail) hBTail
          rw [ihA, ihB]
          change
            (parameter a - parameter b)⁻¹ •
                (A a * orderedProduct A tail -
                  A b * orderedProduct A tail) =
              A a * (A b * orderedProduct A tail)
          rw [← sub_mul]
          rw [hIdentity a b hab]
          rw [smul_mul_assoc, smul_smul]
          rw [inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul]
          rw [mul_assoc]
termination_by s.length

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
