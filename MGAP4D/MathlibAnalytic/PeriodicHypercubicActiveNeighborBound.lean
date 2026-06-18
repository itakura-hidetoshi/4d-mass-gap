import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceCompleteness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped BigOperators

theorem finset_card_biUnion_le_sum_card
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a in s, (f a).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      calc
        ((insert a s).biUnion f).card = (f a ∪ s.biUnion f).card := by
          simp [ha]
        _ ≤ (f a).card + (s.biUnion f).card := Finset.card_union_le
        _ ≤ (f a).card + ∑ b in s, (f b).card :=
          Nat.add_le_add_left ih _
        _ = ∑ b in insert a s, (f b).card := by
          simp [ha]

end

end MathlibAnalytic
end MGAP4D
