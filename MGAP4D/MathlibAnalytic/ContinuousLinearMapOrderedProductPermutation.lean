import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProducts
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem orderedProduct_nil (A : α → E →L[ℝ] E) :
    orderedProduct A [] = 1 := rfl

@[simp] theorem orderedProduct_cons
    (A : α → E →L[ℝ] E) (a : α) (s : List α) :
    orderedProduct A (a :: s) = A a * orderedProduct A s := rfl

/-- If all generators commute, their finite ordered product depends only on the
permutation class of the indexing list. -/
theorem orderedProduct_eq_of_perm_of_pairwise_comm
    (A : α → E →L[ℝ] E)
    (hComm : ∀ a b, A a * A b = A b * A a)
    {s t : List α}
    (hPerm : s.Perm t) :
    orderedProduct A s = orderedProduct A t := by
  induction hPerm with
  | nil => rfl
  | cons a h ih =>
      simp only [orderedProduct_cons]
      rw [ih]
  | swap a b l =>
      simp only [orderedProduct_cons]
      rw [← mul_assoc, hComm a b, mul_assoc]
  | trans hst htu ihst ihtU =>
      exact ihst.trans ihtU

/-- Pointwise form of permutation invariance for commuting finite operator
products. -/
theorem orderedProduct_apply_eq_of_perm_of_pairwise_comm
    (A : α → E →L[ℝ] E)
    (hComm : ∀ a b, A a * A b = A b * A a)
    {s t : List α}
    (hPerm : s.Perm t)
    (x : E) :
    orderedProduct A s x = orderedProduct A t x := by
  rw [orderedProduct_eq_of_perm_of_pairwise_comm A hComm hPerm]

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
