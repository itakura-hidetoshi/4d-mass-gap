import MGAP4D.MathlibAnalytic.ContinuousLinearMapArbitraryPositiveMultiplicityProfileConfluentBinomialNormalForm
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

universe u

variable {α E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every support label of singleton positive jet data has the singleton node. -/
theorem FinitePositivePowerJetData.node_eq_singleton_of_mem_support
    (a : α)
    (m : ℕ)
    (c : ℝ)
    (b : (FinitePositivePowerJetData.singleton a m c).label)
    (_hb : b ∈ (FinitePositivePowerJetData.singleton a m c).support) :
    (FinitePositivePowerJetData.singleton a m c).node b = a := by
  simp [FinitePositivePowerJetData.singleton]

/-- Every support node after one adjoin step is either an old support node or
exactly the newly adjoined node. -/
theorem FinitePositivePowerJetData.adjoin_node_eq_old_or_new
    (d : FinitePositivePowerJetData α)
    (value : α → ℝ)
    (newNode : α)
    (newOrder : ℕ)
    (x : (d.adjoin value newNode newOrder).label)
    (hx : x ∈ (d.adjoin value newNode newOrder).support) :
    (∃ b ∈ d.support,
      (d.adjoin value newNode newOrder).node x = d.node b) ∨
      (d.adjoin value newNode newOrder).node x = newNode := by
  classical
  rcases x with ⟨b, k⟩
  have hxSigma :
      (⟨b, k⟩ : Σ _b : d.label, Sum ℕ ℕ) ∈
        d.support.sigma (fun b =>
          (Finset.range (d.order b + 1)).disjSum
            (Finset.range (newOrder + 1))) := by
    simpa [FinitePositivePowerJetData.adjoin] using hx
  have hbk :
      b ∈ d.support ∧
        k ∈ (Finset.range (d.order b + 1)).disjSum
          (Finset.range (newOrder + 1)) :=
    Finset.mem_sigma.mp hxSigma
  rcases hbk with ⟨hb, _hk⟩
  cases k with
  | inl n =>
      left
      refine ⟨b, hb, ?_⟩
      simp [FinitePositivePowerJetData.adjoin]
  | inr n =>
      right
      simp [FinitePositivePowerJetData.adjoin]

/-- A support-node predicate is preserved by one flattened adjoin step when it
holds for all old support nodes and for the new node. -/
theorem FinitePositivePowerJetData.support_node_property_adjoin
    (d : FinitePositivePowerJetData α)
    (value : α → ℝ)
    (newNode : α)
    (newOrder : ℕ)
    (Q : α → Prop)
    (hOld : ∀ b ∈ d.support, Q (d.node b))
    (hNew : Q newNode) :
    ∀ x ∈ (d.adjoin value newNode newOrder).support,
      Q ((d.adjoin value newNode newOrder).node x) := by
  intro x hx
  rcases d.adjoin_node_eq_old_or_new value newNode newOrder x hx with
    hOrigin | hNewNode
  · rcases hOrigin with ⟨b, hb, hNode⟩
    rw [hNode]
    exact hOld b hb
  · rw [hNewNode]
    exact hNew

/-- Every node predicate holding on the initial support and all folded entries
holds on the final flattened support. -/
theorem positiveMultiplicityProfileDataFrom_support_node
    (value : α → ℝ)
    (d : FinitePositivePowerJetData α)
    (entries : List (PositiveMultiplicityProfileEntry α))
    (Q : α → Prop)
    (hInitial : ∀ b ∈ d.support, Q (d.node b))
    (hEntries : ∀ e ∈ entries, Q e.node) :
    ∀ b ∈ (positiveMultiplicityProfileDataFrom value d entries).support,
      Q ((positiveMultiplicityProfileDataFrom value d entries).node b) := by
  induction entries generalizing d with
  | nil =>
      simpa [positiveMultiplicityProfileDataFrom] using hInitial
  | cons e es ih =>
      apply ih (d := d.adjoin value e.node e.order)
      · exact
          d.support_node_property_adjoin value e.node e.order Q hInitial
            (hEntries e (by simp))
      · intro e' he'
        exact hEntries e' (by simp [he'])

/-- Every final support node originates either in the initial support or in one
of the entries already folded into the flattened jet. -/
theorem positiveMultiplicityProfileDataFrom_node_origin
    (value : α → ℝ)
    (d : FinitePositivePowerJetData α)
    (entries : List (PositiveMultiplicityProfileEntry α))
    (b : (positiveMultiplicityProfileDataFrom value d entries).label)
    (hb : b ∈ (positiveMultiplicityProfileDataFrom value d entries).support) :
    (∃ b₀ ∈ d.support,
      (positiveMultiplicityProfileDataFrom value d entries).node b = d.node b₀) ∨
      ∃ e ∈ entries,
        (positiveMultiplicityProfileDataFrom value d entries).node b = e.node := by
  refine positiveMultiplicityProfileDataFrom_support_node
    value d entries
    (fun a =>
      (∃ b₀ ∈ d.support, a = d.node b₀) ∨
        ∃ e ∈ entries, a = e.node) ?_ ?_ b hb
  · intro b₀ hb₀
    exact Or.inl ⟨b₀, hb₀, rfl⟩
  · intro e he
    exact Or.inr ⟨e, he, rfl⟩

/-- Scalar-value distinctness for two positive multiplicity profile entries. -/
def PositiveMultiplicityProfileEntry.ValueDistinct
    (value : α → ℝ)
    (left right : PositiveMultiplicityProfileEntry α) : Prop :=
  value left.node ≠ value right.node

/-- Natural pairwise scalar distinctness for a nonempty positive multiplicity
profile. -/
def positiveMultiplicityProfilePairwiseDistinct
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) : Prop :=
  (first :: tail).Pairwise
    (PositiveMultiplicityProfileEntry.ValueDistinct value)

/-- Every node in packaged jet data has scalar value distinct from every entry
in the specified list. -/
def FinitePositivePowerJetData.IsValueDistinctFromEntries
    (d : FinitePositivePowerJetData α)
    (value : α → ℝ)
    (entries : List (PositiveMultiplicityProfileEntry α)) : Prop :=
  ∀ b ∈ d.support, ∀ e ∈ entries,
    value (d.node b) ≠ value e.node

/-- Singleton jet data is scalar-distinct from a list whenever its unique node
is scalar-distinct from every entry in that list. -/
theorem FinitePositivePowerJetData.singleton_isValueDistinctFromEntries
    (a : α)
    (m : ℕ)
    (c : ℝ)
    (value : α → ℝ)
    (entries : List (PositiveMultiplicityProfileEntry α))
    (h : ∀ e ∈ entries, value a ≠ value e.node) :
    FinitePositivePowerJetData.IsValueDistinctFromEntries
      (FinitePositivePowerJetData.singleton a m c) value entries := by
  intro b hb e he
  rw [FinitePositivePowerJetData.node_eq_singleton_of_mem_support
    a m c b hb]
  exact h e he

/-- Scalar distinctness from a future list is preserved by one adjoin step when
both all old support nodes and the new node are distinct from that future list. -/
theorem FinitePositivePowerJetData.isValueDistinctFromEntries_adjoin
    (d : FinitePositivePowerJetData α)
    (value : α → ℝ)
    (newNode : α)
    (newOrder : ℕ)
    (entries : List (PositiveMultiplicityProfileEntry α))
    (hOld : d.IsValueDistinctFromEntries value entries)
    (hNew : ∀ e ∈ entries, value newNode ≠ value e.node) :
    FinitePositivePowerJetData.IsValueDistinctFromEntries
      (d.adjoin value newNode newOrder) value entries := by
  intro x hx e he
  rcases d.adjoin_node_eq_old_or_new value newNode newOrder x hx with
    hOrigin | hNewNode
  · rcases hOrigin with ⟨b, hb, hNode⟩
    rw [hNode]
    exact hOld b hb e he
  · rw [hNewNode]
    exact hNew e he

/-- Pairwise scalar distinctness of the remaining entries, together with
scalar distinctness of the current support from all remaining entries, implies
the exact recursive compatibility condition. -/
theorem positiveMultiplicityProfileCompatibleFrom_of_support_pairwise
    (value : α → ℝ)
    (d : FinitePositivePowerJetData α)
    (entries : List (PositiveMultiplicityProfileEntry α))
    (hSupport : d.IsValueDistinctFromEntries value entries)
    (hPairwise : entries.Pairwise
      (PositiveMultiplicityProfileEntry.ValueDistinct value)) :
    positiveMultiplicityProfileCompatibleFrom value d entries := by
  induction entries generalizing d with
  | nil =>
      simp [positiveMultiplicityProfileCompatibleFrom]
  | cons e es ih =>
      cases hPairwise with
      | cons hHead hTail =>
          simp only [positiveMultiplicityProfileCompatibleFrom]
          constructor
          · intro b hb
            exact hSupport b hb e (by simp)
          · apply ih (d := d.adjoin value e.node e.order)
            · exact
                d.isValueDistinctFromEntries_adjoin value e.node e.order es
                  (by
                    intro b hb e' he'
                    exact hSupport b hb e' (by simp [he']))
                  hHead
            · exact hTail

/-- Natural pairwise scalar distinctness of the original nonempty profile
automatically supplies every recursive flattened-support compatibility proof. -/
theorem positiveMultiplicityProfileCompatible_of_pairwise
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail) :
    positiveMultiplicityProfileCompatible value first tail := by
  unfold positiveMultiplicityProfilePairwiseDistinct at hPairwise
  cases hPairwise with
  | cons hFirst hTail =>
      unfold positiveMultiplicityProfileCompatible
      apply positiveMultiplicityProfileCompatibleFrom_of_support_pairwise
      · exact
          FinitePositivePowerJetData.singleton_isValueDistinctFromEntries
            first.node first.order 1 value tail hFirst
      · exact hTail

/-- Pairwise scalar distinctness is sufficient for the arbitrary-length closed
confluent/binomial normal-form identity. -/
theorem positiveMultiplicityProfileData_eval_eq_product_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b)) :
    (positiveMultiplicityProfileData value first tail).eval A =
      positiveMultiplicityProfileProduct A first tail := by
  exact positiveMultiplicityProfileData_eval_eq_product
    A value first tail
    (positiveMultiplicityProfileCompatible_of_pairwise
      value first tail hPairwise)
    hIdentity

/-- Pointwise pairwise-distinct arbitrary-length profile normal-form identity. -/
theorem positiveMultiplicityProfileData_eval_apply_eq_product_apply_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b))
    (x : E) :
    (positiveMultiplicityProfileData value first tail).eval A x =
      positiveMultiplicityProfileProduct A first tail x := by
  exact DFunLike.congr_fun
    (positiveMultiplicityProfileData_eval_eq_product_of_pairwise
      A value first tail hPairwise hIdentity) x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
