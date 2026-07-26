import MGAP4D.MathlibAnalytic.ContinuousLinearMapPermutationCanonicalPositivePowerJetCoefficientMap
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set

namespace ContinuousLinearMap

universe u

variable {α E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The operator family whose finite linear combinations are evaluated by a
positive-power jet coefficient map. -/
noncomputable def positivePowerJetOperatorFamily
    (A : α → E →L[ℝ] E)
    (p : α × ℕ) : E →L[ℝ] E :=
  (A p.1) ^ (p.2 + 1)

/-- Global semantic faithfulness of positive-power jet coefficients for one
operator family.  This is exactly linear independence of every node-order
operator power. -/
def PositivePowerJetCoefficientMap.IsOperatorIndependent
    (A : α → E →L[ℝ] E) : Prop :=
  LinearIndependent ℝ (positivePowerJetOperatorFamily A)

/-- The support-local independence condition needed to compare two specific
coefficient maps.  No independence is requested outside the finite union of
their supports. -/
def PositivePowerJetCoefficientMap.AreOperatorIndependentOnSupport
    (c d : PositivePowerJetCoefficientMap α)
    (A : α → E →L[ℝ] E) : Prop :=
  LinearIndepOn ℝ (positivePowerJetOperatorFamily A)
    (↑(c.support ∪ d.support) : Set (α × ℕ))

/-- Positive-power jet evaluation is the standard finitely supported linear
combination of the node-order operator family. -/
theorem PositivePowerJetCoefficientMap.eval_eq_linearCombination
    (c : PositivePowerJetCoefficientMap α)
    (A : α → E →L[ℝ] E) :
    PositivePowerJetCoefficientMap.eval c A =
      Finsupp.linearCombination ℝ (positivePowerJetOperatorFamily A) c := by
  classical
  simp [PositivePowerJetCoefficientMap.eval,
    positivePowerJetCoefficientTerm,
    positivePowerJetOperatorFamily,
    Finsupp.linearCombination_apply]

/-- Global operator independence is equivalent to injectivity of coefficient
map evaluation. -/
theorem PositivePowerJetCoefficientMap.isOperatorIndependent_iff_eval_injective
    (A : α → E →L[ℝ] E) :
    PositivePowerJetCoefficientMap.IsOperatorIndependent A ↔
      Function.Injective
        (fun c : PositivePowerJetCoefficientMap α =>
          PositivePowerJetCoefficientMap.eval c A) := by
  constructor
  · intro hIndependent c d hEval
    apply hIndependent.finsuppLinearCombination_injective
    simpa only [PositivePowerJetCoefficientMap.eval_eq_linearCombination] using hEval
  · intro hEval
    unfold PositivePowerJetCoefficientMap.IsOperatorIndependent
    unfold LinearIndependent
    intro c d hCombination
    apply hEval
    simpa only [PositivePowerJetCoefficientMap.eval_eq_linearCombination] using hCombination

/-- Global independence implies the exact support-local condition for every
pair of finite coefficient maps. -/
theorem PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_isOperatorIndependent
    (A : α → E →L[ℝ] E)
    (hIndependent : PositivePowerJetCoefficientMap.IsOperatorIndependent A)
    (c d : PositivePowerJetCoefficientMap α) :
    c.AreOperatorIndependentOnSupport d A := by
  exact hIndependent.linearIndepOn _

/-- Equal operator evaluations have equal coefficients whenever the relevant
finite node-order family is linearly independent. -/
theorem PositivePowerJetCoefficientMap.eq_of_eval_eq_of_areOperatorIndependentOnSupport
    (c d : PositivePowerJetCoefficientMap α)
    (A : α → E →L[ℝ] E)
    (hIndependent : c.AreOperatorIndependentOnSupport d A)
    (hEval : PositivePowerJetCoefficientMap.eval c A =
      PositivePowerJetCoefficientMap.eval d A) :
    c = d := by
  have hc : c ∈ Finsupp.supported ℝ ℝ
      (↑(c.support ∪ d.support) : Set (α × ℕ)) := by
    rw [Finsupp.mem_supported]
    exact Finset.coe_subset.mpr Finset.subset_union_left
  have hd : d ∈ Finsupp.supported ℝ ℝ
      (↑(c.support ∪ d.support) : Set (α × ℕ)) := by
    rw [Finsupp.mem_supported]
    exact Finset.coe_subset.mpr Finset.subset_union_right
  apply (linearIndepOn_iffₛ.mp hIndependent) c hc d hd
  simpa only [PositivePowerJetCoefficientMap.eval_eq_linearCombination] using hEval

/-- Global independence turns operator equality into coefficient equality. -/
theorem PositivePowerJetCoefficientMap.eq_of_eval_eq_of_isOperatorIndependent
    (c d : PositivePowerJetCoefficientMap α)
    (A : α → E →L[ℝ] E)
    (hIndependent : PositivePowerJetCoefficientMap.IsOperatorIndependent A)
    (hEval : PositivePowerJetCoefficientMap.eval c A =
      PositivePowerJetCoefficientMap.eval d A) :
    c = d := by
  exact c.eq_of_eval_eq_of_areOperatorIndependentOnSupport d A
    (PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_isOperatorIndependent
      A hIndependent c d) hEval

/-- Under support-local operator independence, two pairwise-distinct orderings
of the same profile have exactly the same recursively aggregated coefficient
map, not merely the same operator evaluation. -/
theorem positiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_supportIndependent
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      positiveMultiplicityProfilePairwiseDistinct value first₁ tail₁)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b))
    (hIndependent :
      (positiveMultiplicityProfileCoefficientMap value first₁ tail₁).
        AreOperatorIndependentOnSupport
          (positiveMultiplicityProfileCoefficientMap value first₂ tail₂) A) :
    positiveMultiplicityProfileCoefficientMap value first₁ tail₁ =
      positiveMultiplicityProfileCoefficientMap value first₂ tail₂ := by
  have hPairwise₂ :
      positiveMultiplicityProfilePairwiseDistinct value first₂ tail₂ := by
    unfold positiveMultiplicityProfilePairwiseDistinct at hPairwise₁ ⊢
    exact pairwise_of_perm_of_symmetric
      (PositiveMultiplicityProfileEntry.valueDistinct_symmetric value)
      hPerm hPairwise₁
  apply PositivePowerJetCoefficientMap.eq_of_eval_eq_of_areOperatorIndependentOnSupport
    _ _ A hIndependent
  rw [positiveMultiplicityProfileCoefficientMap_eval_eq_product_of_pairwise
    A value first₁ tail₁ hPairwise₁ hIdentity]
  rw [positiveMultiplicityProfileCoefficientMap_eval_eq_product_of_pairwise
    A value first₂ tail₂ hPairwise₂ hIdentity]
  exact positiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
    A value first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hIdentity

/-- Global operator independence gives exact permutation invariance of the
older recursively aggregated coefficient maps. -/
theorem positiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_operatorIndependent
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      positiveMultiplicityProfilePairwiseDistinct value first₁ tail₁)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b))
    (hIndependent : PositivePowerJetCoefficientMap.IsOperatorIndependent A) :
    positiveMultiplicityProfileCoefficientMap value first₁ tail₁ =
      positiveMultiplicityProfileCoefficientMap value first₂ tail₂ := by
  apply positiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_supportIndependent
    A value first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hIdentity
  exact PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_isOperatorIndependent
    A hIndependent _ _

/-- Under support-local independence, the permutation-canonical representative
is the older recursively aggregated coefficient map itself. -/
theorem positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_supportIndependent
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b))
    (hIndependent :
      (positiveMultiplicityProfilePermutationCanonicalCoefficientMap
          value first tail).AreOperatorIndependentOnSupport
        (positiveMultiplicityProfileCoefficientMap value first tail) A) :
    positiveMultiplicityProfilePermutationCanonicalCoefficientMap
        value first tail =
      positiveMultiplicityProfileCoefficientMap value first tail := by
  apply PositivePowerJetCoefficientMap.eq_of_eval_eq_of_areOperatorIndependentOnSupport
    _ _ A hIndependent
  exact
    positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_eq_coefficientMap_eval_of_pairwise
      A value first tail hPairwise hIdentity

/-- Under global independence, the permutation-canonical representative equals
the older recursively aggregated coefficient map. -/
theorem positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_operatorIndependent
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b))
    (hIndependent : PositivePowerJetCoefficientMap.IsOperatorIndependent A) :
    positiveMultiplicityProfilePermutationCanonicalCoefficientMap
        value first tail =
      positiveMultiplicityProfileCoefficientMap value first tail := by
  apply
    positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_supportIndependent
      A value first tail hPairwise hIdentity
  exact PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_isOperatorIndependent
    A hIndependent _ _

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
