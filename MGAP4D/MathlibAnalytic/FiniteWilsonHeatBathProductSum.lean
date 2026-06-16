import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite sum is invariant under reindexing by an equivalence.  This small
bridge isolates the purely finite combinatorics used by heat-bath detailed
balance. -/
theorem finite_sum_comp_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (g : β → ℝ) :
    (∑ x : α, g (e x)) = ∑ y : β, g y :=
  e.sum_comp g

end

end MathlibAnalytic
end MGAP4D
