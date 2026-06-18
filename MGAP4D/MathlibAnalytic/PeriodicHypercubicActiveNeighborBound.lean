import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Lemmas
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

/-- The cardinality of a finite union is bounded by the sum of the
cardinalities of its members. -/
theorem finset_card_biUnion_le_sum_card
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      calc
        ((insert a s).biUnion f).card ≤
            (f a).card + (s.biUnion f).card :=
          finset_card_biUnion_insert_le a s f
        _ ≤ (f a).card + ∑ b ∈ s, (f b).card :=
          Nat.add_le_add_left ih _
        _ = ∑ b ∈ insert a s, (f b).card := by
          rw [Finset.sum_insert ha]

end

end MathlibAnalytic
end MGAP4D
