import MGAP4D.MathlibAnalytic.ContinuousLinearMapCanonicalPositivePowerJetCoefficientMap
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

universe u

variable {α E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scalar-first lexicographic ordering key for a multiplicity-profile entry.
The multiplicity order breaks ties at one scalar node. -/
def PositiveMultiplicityProfileEntry.sortKey
    (value : α → ℝ)
    (e : PositiveMultiplicityProfileEntry α) :
    ℝ ×ₗ ℕ :=
  toLex (value e.node, e.order)

/-- The profile-entry sorting key is injective whenever the scalar-value map is
injective on physical nodes. -/
theorem PositiveMultiplicityProfileEntry.sortKey_injective
    (value : α → ℝ)
    (hValueInjective : Function.Injective value) :
    Function.Injective
      (PositiveMultiplicityProfileEntry.sortKey value) := by
  intro left right h
  have hPair := congrArg
    (fun x : ℝ ×ₗ ℕ => ofLex x) h
  cases left with
  | mk leftNode leftOrder =>
      cases right with
      | mk rightNode rightOrder =>
          have hNode : leftNode = rightNode :=
            hValueInjective (congrArg Prod.fst hPair)
          have hOrder : leftOrder = rightOrder :=
            congrArg Prod.snd hPair
          cases hNode
          cases hOrder
          rfl

/-- Canonical total ordering relation used to select one representative of a
multiplicity-profile permutation class. -/
def PositiveMultiplicityProfileEntry.sortLE
    (value : α → ℝ)
    (left right : PositiveMultiplicityProfileEntry α) : Prop :=
  PositiveMultiplicityProfileEntry.sortKey value left ≤
    PositiveMultiplicityProfileEntry.sortKey value right

instance positiveMultiplicityProfileEntrySortLETotal
    (value : α → ℝ) :
    Std.Total (PositiveMultiplicityProfileEntry.sortLE value) :=
  ⟨fun left right => le_total
    (PositiveMultiplicityProfileEntry.sortKey value left)
    (PositiveMultiplicityProfileEntry.sortKey value right)⟩

instance positiveMultiplicityProfileEntrySortLETrans
    (value : α → ℝ) :
    IsTrans (PositiveMultiplicityProfileEntry α)
      (PositiveMultiplicityProfileEntry.sortLE value) :=
  ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

/-- Pairwiseness for a symmetric relation is invariant under list
permutations. -/
theorem pairwise_of_perm_of_symmetric
    {γ : Type*}
    {R : γ → γ → Prop}
    (hSymm : ∀ a b, R a b → R b a)
    {entries₁ entries₂ : List γ}
    (hPerm : entries₁.Perm entries₂)
    (hPairwise : entries₁.Pairwise R) :
    entries₂.Pairwise R := by
  induction hPerm with
  | nil =>
      exact .nil
  | @cons a entries₁ entries₂ hPerm ih =>
      cases hPairwise with
      | cons hHead hTail =>
          constructor
          · intro b hb
            exact hHead b ((hPerm.mem_iff).mpr hb)
          · exact ih hTail
  | @swap a b entries =>
      cases hPairwise with
      | cons hB hRest =>
          cases hRest with
          | cons hA hTail =>
              constructor
              · intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with hxb | hx
                · rw [hxb]
                  exact hSymm b a (hB a (by simp))
                · exact hA x hx
              · constructor
                · intro x hx
                  exact hB x (List.mem_cons.mpr (Or.inr hx))
                · exact hTail
  | @trans entries₁ entries₂ entries₃ hPerm₁ hPerm₂ ih₁ ih₂ =>
      exact ih₂ (ih₁ hPairwise)

/-- Scalar-value distinctness is symmetric. -/
theorem PositiveMultiplicityProfileEntry.valueDistinct_symmetric
    (value : α → ℝ)
    (left right : PositiveMultiplicityProfileEntry α) :
    left.ValueDistinct value right → right.ValueDistinct value left := by
  intro h
  exact h.symm

/-- The deterministically sorted entry list of a nonempty multiplicity profile. -/
noncomputable def positiveMultiplicityProfileSortedEntries
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    List (PositiveMultiplicityProfileEntry α) := by
  classical
  exact List.mergeSort (first :: tail)
    (fun left right =>
      decide (PositiveMultiplicityProfileEntry.sortLE value left right))

/-- Sorting preserves the original multiplicity-profile multiset. -/
theorem positiveMultiplicityProfileSortedEntries_perm
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    (positiveMultiplicityProfileSortedEntries value first tail).Perm
      (first :: tail) := by
  classical
  simpa [positiveMultiplicityProfileSortedEntries] using
    (List.mergeSort_perm (first :: tail)
      (fun left right =>
        decide (PositiveMultiplicityProfileEntry.sortLE value left right)))

/-- The selected representative is sorted by the canonical entry order. -/
theorem positiveMultiplicityProfileSortedEntries_pairwise
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    (positiveMultiplicityProfileSortedEntries value first tail).Pairwise
      (PositiveMultiplicityProfileEntry.sortLE value) := by
  classical
  simpa [positiveMultiplicityProfileSortedEntries] using
    (List.pairwise_mergeSort'
      (PositiveMultiplicityProfileEntry.sortLE value) (first :: tail))

/-- Two permutations have exactly the same deterministically sorted entry list
when scalar values determine physical nodes. -/
theorem positiveMultiplicityProfileSortedEntries_eq_of_perm
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hValueInjective : Function.Injective value)
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂)) :
    positiveMultiplicityProfileSortedEntries value first₁ tail₁ =
      positiveMultiplicityProfileSortedEntries value first₂ tail₂ := by
  classical
  letI : Std.Antisymm
      (PositiveMultiplicityProfileEntry.sortLE value) :=
    ⟨fun _ _ h₁ h₂ =>
      PositiveMultiplicityProfileEntry.sortKey_injective
        value hValueInjective (le_antisymm h₁ h₂)⟩
  have hSortedPerm :
      (positiveMultiplicityProfileSortedEntries value first₁ tail₁).Perm
        (positiveMultiplicityProfileSortedEntries value first₂ tail₂) :=
    (positiveMultiplicityProfileSortedEntries_perm value first₁ tail₁).trans
      (hPerm.trans
        (positiveMultiplicityProfileSortedEntries_perm
          value first₂ tail₂).symm)
  exact hSortedPerm.eq_of_pairwise'
    (positiveMultiplicityProfileSortedEntries_pairwise
      value first₁ tail₁)
    (positiveMultiplicityProfileSortedEntries_pairwise
      value first₂ tail₂)

/-- The sorted representative of a nonempty profile is nonempty. -/
theorem positiveMultiplicityProfileSortedEntries_ne_nil
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    positiveMultiplicityProfileSortedEntries value first tail ≠ [] := by
  intro hNil
  have hPerm := positiveMultiplicityProfileSortedEntries_perm
    value first tail
  rw [hNil] at hPerm
  exact List.not_perm_nil_cons first tail hPerm

/-- A genuinely permutation-canonical coefficient-map representative: sort the
profile by scalar value and multiplicity order, then run the existing
confluent/binomial coefficient aggregation on that unique ordering. -/
noncomputable def positiveMultiplicityProfilePermutationCanonicalCoefficientMap
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    PositivePowerJetCoefficientMap α :=
  match positiveMultiplicityProfileSortedEntries value first tail with
  | [] => 0
  | sortedFirst :: sortedTail =>
      positiveMultiplicityProfileCoefficientMap
        value sortedFirst sortedTail

/-- The canonical coefficient Finsupp is independent of the input ordering
when the scalar-value map is injective. -/
theorem positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_of_perm
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hValueInjective : Function.Injective value)
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂)) :
    positiveMultiplicityProfilePermutationCanonicalCoefficientMap
        value first₁ tail₁ =
      positiveMultiplicityProfilePermutationCanonicalCoefficientMap
        value first₂ tail₂ := by
  rw [positiveMultiplicityProfilePermutationCanonicalCoefficientMap,
    positiveMultiplicityProfilePermutationCanonicalCoefficientMap,
    positiveMultiplicityProfileSortedEntries_eq_of_perm
      value first₁ first₂ tail₁ tail₂ hValueInjective hPerm]

/-- Pairwise scalar distinctness is inherited by the selected sorted
representative. -/
theorem positiveMultiplicityProfileSortedEntries_pairwiseDistinct
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail) :
    (positiveMultiplicityProfileSortedEntries value first tail).Pairwise
      (PositiveMultiplicityProfileEntry.ValueDistinct value) := by
  unfold positiveMultiplicityProfilePairwiseDistinct at hPairwise
  exact pairwise_of_perm_of_symmetric
    (PositiveMultiplicityProfileEntry.valueDistinct_symmetric value)
    (positiveMultiplicityProfileSortedEntries_perm
      value first tail).symm hPairwise

/-- Under pairwise scalar distinctness, the permutation-canonical coefficient
map evaluates to the original mixed operator product. -/
theorem positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_eq_product_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b)) :
    PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfilePermutationCanonicalCoefficientMap
          value first tail) A =
      positiveMultiplicityProfileProduct A first tail := by
  classical
  cases hSorted : positiveMultiplicityProfileSortedEntries
      value first tail with
  | nil =>
      exact False.elim
        (positiveMultiplicityProfileSortedEntries_ne_nil
          value first tail hSorted)
  | cons sortedFirst sortedTail =>
      have hPermSorted :
          (sortedFirst :: sortedTail).Perm (first :: tail) := by
        have hPerm := positiveMultiplicityProfileSortedEntries_perm
          value first tail
        simpa [hSorted] using hPerm
      have hPairwiseSorted :
          positiveMultiplicityProfilePairwiseDistinct
            value sortedFirst sortedTail := by
        unfold positiveMultiplicityProfilePairwiseDistinct
        have hSortedDistinct :=
          positiveMultiplicityProfileSortedEntries_pairwiseDistinct
            value first tail hPairwise
        simpa [hSorted] using hSortedDistinct
      rw [positiveMultiplicityProfilePermutationCanonicalCoefficientMap,
        hSorted]
      calc
        PositivePowerJetCoefficientMap.eval
            (positiveMultiplicityProfileCoefficientMap
              value sortedFirst sortedTail) A =
          positiveMultiplicityProfileProduct A sortedFirst sortedTail :=
            positiveMultiplicityProfileCoefficientMap_eval_eq_product_of_pairwise
              A value sortedFirst sortedTail hPairwiseSorted hIdentity
        _ = positiveMultiplicityProfileProduct A first tail :=
            positiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
              A value sortedFirst first sortedTail tail hPermSorted
                hPairwiseSorted hIdentity

/-- The selected canonical representative and the original recursively
aggregated coefficient map have identical operator semantics. -/
theorem positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_eq_coefficientMap_eval_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b)) :
    PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfilePermutationCanonicalCoefficientMap
          value first tail) A =
      PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfileCoefficientMap value first tail) A := by
  rw [positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_eq_product_of_pairwise
    A value first tail hPairwise hIdentity]
  rw [positiveMultiplicityProfileCoefficientMap_eval_eq_product_of_pairwise
    A value first tail hPairwise hIdentity]

/-- Pointwise form of the canonical representative identity. -/
theorem positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_apply_eq_product_apply_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b))
    (x : E) :
    PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfilePermutationCanonicalCoefficientMap
          value first tail) A x =
      positiveMultiplicityProfileProduct A first tail x := by
  exact DFunLike.congr_fun
    (positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_eq_product_of_pairwise
      A value first tail hPairwise hIdentity) x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
