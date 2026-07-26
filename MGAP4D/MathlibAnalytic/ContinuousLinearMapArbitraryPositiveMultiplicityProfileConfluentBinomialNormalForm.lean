import MGAP4D.MathlibAnalytic.ContinuousLinearMapFinitePositivePowerJetAdjoinConfluentBinomialNormalForm
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

universe u

variable {α E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite labelled data for a positive power-jet combination.  The internal
label type is existentially packaged, so one adjoin step may refine the labels
without changing the outer data type. -/
structure FinitePositivePowerJetData (α : Type u) where
  label : Type
  support : Finset label
  node : label → α
  order : label → ℕ
  coefficient : label → ℝ

/-- Evaluation of packaged finite positive power-jet data. -/
noncomputable def FinitePositivePowerJetData.eval
    (d : FinitePositivePowerJetData α)
    (A : α → E →L[ℝ] E) : E →L[ℝ] E :=
  finitePositivePowerJetCombination
    A d.support d.node d.order d.coefficient

/-- One node and its zero-based positive multiplicity order. -/
structure PositiveMultiplicityProfileEntry (α : Type u) where
  node : α
  order : ℕ

/-- Singleton positive power-jet data. -/
noncomputable def FinitePositivePowerJetData.singleton
    (a : α) (m : ℕ) (c : ℝ := 1) :
    FinitePositivePowerJetData α := by
  classical
  exact
    { label := Unit
      support := {()}
      node := fun _ => a
      order := fun _ => m
      coefficient := fun _ => c }

/-- Evaluation of singleton jet data. -/
@[simp] theorem FinitePositivePowerJetData.eval_singleton
    (A : α → E →L[ℝ] E)
    (a : α) (m : ℕ) (c : ℝ) :
    (FinitePositivePowerJetData.singleton a m c).eval A =
      c • (A a) ^ (m + 1) := by
  classical
  simp [FinitePositivePowerJetData.eval,
    FinitePositivePowerJetData.singleton,
    finitePositivePowerJetCombination,
    finitePowerJetCombination]

/-- Exact scalar distinctness condition for adjoining one new node to packaged
finite positive jet data. -/
def FinitePositivePowerJetData.IsCompatibleWith
    (d : FinitePositivePowerJetData α)
    (value : α → ℝ)
    (newNode : α) : Prop :=
  ∀ b ∈ d.support, value (d.node b) ≠ value newNode

/-- Refine finite positive jet data by adjoining one new positive-multiplicity
node and flattening every two-node binomial expansion back into labelled pure
powers. -/
noncomputable def FinitePositivePowerJetData.adjoin
    (d : FinitePositivePowerJetData α)
    (value : α → ℝ)
    (newNode : α)
    (newOrder : ℕ) :
    FinitePositivePowerJetData α := by
  classical
  let NewLabel := Σ _b : d.label, Sum ℕ ℕ
  let fiber : d.label → Finset (Sum ℕ ℕ) := fun b =>
    (Finset.range (d.order b + 1)).disjSum
      (Finset.range (newOrder + 1))
  let node : NewLabel → α := fun x =>
    match x.2 with
    | Sum.inl _ => d.node x.1
    | Sum.inr _ => newNode
  let order : NewLabel → ℕ := fun x =>
    match x.2 with
    | Sum.inl k => k
    | Sum.inr k => k
  let coefficient : NewLabel → ℝ := fun x =>
    match x.2 with
    | Sum.inl k =>
        d.coefficient x.1 *
          twoSidedConfluentLeftBinomialCoefficient
            (value (d.node x.1) - value newNode)⁻¹
            (d.order x.1) newOrder k
    | Sum.inr k =>
        d.coefficient x.1 *
          twoSidedConfluentRightBinomialCoefficient
            (value (d.node x.1) - value newNode)⁻¹
            (d.order x.1) newOrder k
  exact
    { label := NewLabel
      support := d.support.sigma fiber
      node := node
      order := order
      coefficient := coefficient }

/-- Evaluation of the flattened adjoin data is exactly the termwise closed
binomial adjoin normal form. -/
theorem FinitePositivePowerJetData.eval_adjoin_eq_normalForm
    (d : FinitePositivePowerJetData α)
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (newNode : α)
    (newOrder : ℕ) :
    (d.adjoin value newNode newOrder).eval A =
      finitePositivePowerJetAdjoinConfluentBinomialNormalForm
        A value d.support d.node d.order d.coefficient
          newNode newOrder := by
  classical
  simp [FinitePositivePowerJetData.eval,
    FinitePositivePowerJetData.adjoin,
    finitePositivePowerJetCombination,
    finitePowerJetCombination,
    finitePositivePowerJetAdjoinConfluentBinomialNormalForm,
    twoSidedConfluentResolventBinomialNormalForm,
    twoSidedConfluentLeftBinomialSum,
    twoSidedConfluentRightBinomialSum,
    Finset.sum_sigma, Finset.sum_disjSum, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]

/-- One flattened adjoin step evaluates to right multiplication by the new
positive resolvent power. -/
theorem FinitePositivePowerJetData.eval_adjoin_eq_mul_pow_succ
    (d : FinitePositivePowerJetData α)
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (newNode : α)
    (newOrder : ℕ)
    (hne : d.IsCompatibleWith value newNode)
    (hIdentity : ∀ b ∈ d.support,
      A (d.node b) - A newNode =
        (value (d.node b) - value newNode) •
          (A (d.node b) * A newNode)) :
    (d.adjoin value newNode newOrder).eval A =
      d.eval A * (A newNode) ^ (newOrder + 1) := by
  calc
    (d.adjoin value newNode newOrder).eval A =
        finitePositivePowerJetAdjoinConfluentBinomialNormalForm
          A value d.support d.node d.order d.coefficient
            newNode newOrder :=
      d.eval_adjoin_eq_normalForm A value newNode newOrder
    _ = d.eval A * (A newNode) ^ (newOrder + 1) := by
      rw [FinitePositivePowerJetData.eval]
      exact
        (finitePositivePowerJetCombination_mul_pow_succ_eq_adjoinConfluentBinomialNormalForm
          A value d.support d.node d.order d.coefficient
            newNode newOrder hne hIdentity).symm

/-- Fold a list of right-adjoined positive-multiplicity nodes through packaged
finite jet data. -/
noncomputable def positiveMultiplicityProfileDataFrom
    (value : α → ℝ)
    (d : FinitePositivePowerJetData α)
    (entries : List (PositiveMultiplicityProfileEntry α)) :
    FinitePositivePowerJetData α :=
  match entries with
  | [] => d
  | e :: es =>
      positiveMultiplicityProfileDataFrom value
        (d.adjoin value e.node e.order) es

/-- The corresponding left-associated operator product fold. -/
noncomputable def positiveMultiplicityProfileProductFrom
    (A : α → E →L[ℝ] E)
    (T : E →L[ℝ] E)
    (entries : List (PositiveMultiplicityProfileEntry α)) :
    E →L[ℝ] E :=
  match entries with
  | [] => T
  | e :: es =>
      positiveMultiplicityProfileProductFrom A
        (T * (A e.node) ^ (e.order + 1)) es

/-- Recursive exact compatibility condition for the successive flattened
adjoin steps of a positive multiplicity profile. -/
def positiveMultiplicityProfileCompatibleFrom
    (value : α → ℝ)
    (d : FinitePositivePowerJetData α)
    (entries : List (PositiveMultiplicityProfileEntry α)) : Prop :=
  match entries with
  | [] => True
  | e :: es =>
      d.IsCompatibleWith value e.node ∧
        positiveMultiplicityProfileCompatibleFrom value
          (d.adjoin value e.node e.order) es

/-- Arbitrary nonempty positive multiplicity profile data, starting from one
node and folding the remaining nodes by flattened binomial adjoin steps. -/
noncomputable def positiveMultiplicityProfileData
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    FinitePositivePowerJetData α :=
  positiveMultiplicityProfileDataFrom value
    (FinitePositivePowerJetData.singleton first.node first.order) tail

/-- Operator product associated with an arbitrary nonempty positive
multiplicity profile. -/
noncomputable def positiveMultiplicityProfileProduct
    (A : α → E →L[ℝ] E)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    E →L[ℝ] E :=
  positiveMultiplicityProfileProductFrom A
    ((A first.node) ^ (first.order + 1)) tail

/-- Exact recursive compatibility condition for an arbitrary nonempty positive
multiplicity profile. -/
def positiveMultiplicityProfileCompatible
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) : Prop :=
  positiveMultiplicityProfileCompatibleFrom value
    (FinitePositivePowerJetData.singleton first.node first.order) tail

/-- The flattened finite jet data of every compatible nonempty profile evaluates
exactly to its arbitrary-length mixed resolvent product. -/
theorem positiveMultiplicityProfileDataFrom_eval_eq_productFrom
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (d : FinitePositivePowerJetData α)
    (entries : List (PositiveMultiplicityProfileEntry α))
    (hCompatible :
      positiveMultiplicityProfileCompatibleFrom value d entries)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b)) :
    (positiveMultiplicityProfileDataFrom value d entries).eval A =
      positiveMultiplicityProfileProductFrom A (d.eval A) entries := by
  induction entries generalizing d with
  | nil => rfl
  | cons e es ih =>
      rcases hCompatible with ⟨hne, hTail⟩
      simp only [positiveMultiplicityProfileDataFrom,
        positiveMultiplicityProfileProductFrom]
      rw [ih (d := d.adjoin value e.node e.order) hTail]
      rw [d.eval_adjoin_eq_mul_pow_succ A value e.node e.order hne]
      intro b hb
      exact hIdentity (d.node b) e.node

/-- Arbitrary-length closed confluent/binomial normal form for a compatible
nonempty positive multiplicity profile. -/
theorem positiveMultiplicityProfileData_eval_eq_product
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hCompatible :
      positiveMultiplicityProfileCompatible value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b)) :
    (positiveMultiplicityProfileData value first tail).eval A =
      positiveMultiplicityProfileProduct A first tail := by
  simpa [positiveMultiplicityProfileData,
    positiveMultiplicityProfileProduct] using
    (positiveMultiplicityProfileDataFrom_eval_eq_productFrom
      A value
      (FinitePositivePowerJetData.singleton first.node first.order)
      tail hCompatible hIdentity)

/-- Pointwise arbitrary-length profile normal-form identity. -/
theorem positiveMultiplicityProfileData_eval_apply_eq_product_apply
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hCompatible :
      positiveMultiplicityProfileCompatible value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b))
    (x : E) :
    (positiveMultiplicityProfileData value first tail).eval A x =
      positiveMultiplicityProfileProduct A first tail x := by
  exact DFunLike.congr_fun
    (positiveMultiplicityProfileData_eval_eq_product
      A value first tail hCompatible hIdentity) x

/-- Every packaged finite positive jet is exactly the finite ordered-word sum
of its replicated pure-power words. -/
theorem FinitePositivePowerJetData.eval_eq_finset_sum_smul_orderedProduct_replicate
    (d : FinitePositivePowerJetData α)
    (A : α → E →L[ℝ] E) :
    d.eval A =
      d.support.sum (fun b => d.coefficient b •
        orderedProduct A (List.replicate (d.order b + 1) (d.node b))) := by
  simpa [FinitePositivePowerJetData.eval,
    finitePositivePowerJetCombination] using
    (finitePowerJetCombination_eq_finset_sum_smul_orderedProduct_replicate
      A d.support d.node (fun b => d.order b + 1) d.coefficient)

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
