import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProducts
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {α β E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A repeated copy of one operator generator has ordered product equal to the
corresponding finite operator power. -/
@[simp] theorem orderedProduct_replicate
    (A : α → E →L[ℝ] E)
    (a : α) :
    ∀ n : ℕ, orderedProduct A (List.replicate n a) = (A a) ^ n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate_succ, orderedProduct, ih, pow_succ']

/-- A finite operator power-jet combination is a finite real linear combination
of powers evaluated at finitely many labelled nodes.  Distinct labels may carry
the same node, so this surface allows arbitrary repeated-node multiplicities. -/
noncomputable def finitePowerJetCombination
    (A : α → E →L[ℝ] E)
    (s : Finset β)
    (node : β → α)
    (order : β → ℕ)
    (c : β → ℝ) :
    E →L[ℝ] E :=
  s.sum (fun b => c b • ((A (node b)) ^ (order b)))

/-- The finite power-jet combination is exactly the finite ordered-word sum
obtained by repeating each labelled node according to its multiplicity. -/
theorem finitePowerJetCombination_eq_finset_sum_smul_orderedProduct_replicate
    (A : α → E →L[ℝ] E)
    (s : Finset β)
    (node : β → α)
    (order : β → ℕ)
    (c : β → ℝ) :
    finitePowerJetCombination A s node order c =
      s.sum (fun b => c b •
        orderedProduct A (List.replicate (order b) (node b))) := by
  simp [finitePowerJetCombination]

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
