import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceCompleteness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped BigOperators

/-- Adding one index to a finite union increases cardinality by at most the
cardinality of the newly added finset. -/
theorem finset_card_biUnion_insert_le
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (a : α) (s : Finset α) (f : α → Finset β) :
    ((insert a s).biUnion f).card ≤
      (f a).card + (s.biUnion f).card := by
  rw [Finset.biUnion_insert]
  exact Finset.card_union_le (f a) (s.biUnion f)

end

end MathlibAnalytic
end MGAP4D
