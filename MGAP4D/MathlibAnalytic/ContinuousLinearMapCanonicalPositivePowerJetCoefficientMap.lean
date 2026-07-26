import MGAP4D.MathlibAnalytic.ContinuousLinearMapPositiveMultiplicityProfilePermutationInvariantNormalForm
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

universe u

variable {α E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Canonical coefficient data for a finite positive power jet.  The key is the
physical node together with the zero-based positive-power order, so all labels
carrying the same node and order are aggregated by addition. -/
abbrev PositivePowerJetCoefficientMap (α : Type u) :=
  (α × ℕ) →₀ ℝ

/-- The additive operator-valued term associated with one canonical jet key. -/
noncomputable def positivePowerJetCoefficientTerm
    (A : α → E →L[ℝ] E)
    (p : α × ℕ) : ℝ →+ E →L[ℝ] E where
  toFun c := c • (A p.1) ^ (p.2 + 1)
  map_zero' := by simp
  map_add' x y := by simp [add_smul]

/-- Evaluation of a canonical positive-power coefficient map. -/
noncomputable def PositivePowerJetCoefficientMap.eval
    (c : PositivePowerJetCoefficientMap α)
    (A : α → E →L[ℝ] E) : E →L[ℝ] E :=
  Finsupp.liftAddHom (fun p => positivePowerJetCoefficientTerm A p) c

@[simp] theorem PositivePowerJetCoefficientMap.eval_zero
    (A : α → E →L[ℝ] E) :
    PositivePowerJetCoefficientMap.eval
      (0 : PositivePowerJetCoefficientMap α) A = 0 := by
  simp [PositivePowerJetCoefficientMap.eval]

@[simp] theorem PositivePowerJetCoefficientMap.eval_single
    (A : α → E →L[ℝ] E)
    (p : α × ℕ)
    (c : ℝ) :
    PositivePowerJetCoefficientMap.eval
        (Finsupp.single p c : PositivePowerJetCoefficientMap α) A =
      c • (A p.1) ^ (p.2 + 1) := by
  simp [PositivePowerJetCoefficientMap.eval,
    positivePowerJetCoefficientTerm]

/-- Aggregate all labelled coefficients of packaged finite positive jet data by
physical node and zero-based order. -/
noncomputable def FinitePositivePowerJetData.coefficientMap
    (d : FinitePositivePowerJetData α) :
    PositivePowerJetCoefficientMap α :=
  d.support.sum (fun b =>
    Finsupp.single (d.node b, d.order b) (d.coefficient b))

/-- Pointwise formula for the aggregated coefficient at one node-order key. -/
theorem FinitePositivePowerJetData.coefficientMap_apply
    [DecidableEq α]
    (d : FinitePositivePowerJetData α)
    (p : α × ℕ) :
    d.coefficientMap p =
      d.support.sum (fun b =>
        if (d.node b, d.order b) = p then d.coefficient b else 0) := by
  classical
  rw [FinitePositivePowerJetData.coefficientMap]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : (d.node b, d.order b) = p
  · subst p
    simp
  · rw [Finsupp.single_eq_of_ne' h]
    simp [h]

/-- Canonical aggregation preserves the operator evaluation exactly, including
zero coefficients and arbitrarily repeated internal labels. -/
theorem FinitePositivePowerJetData.coefficientMap_eval_eq
    (d : FinitePositivePowerJetData α)
    (A : α → E →L[ℝ] E) :
    PositivePowerJetCoefficientMap.eval d.coefficientMap A = d.eval A := by
  classical
  simp [FinitePositivePowerJetData.coefficientMap,
    PositivePowerJetCoefficientMap.eval,
    positivePowerJetCoefficientTerm,
    FinitePositivePowerJetData.eval,
    finitePositivePowerJetCombination,
    finitePowerJetCombination]

/-- Equality of canonical coefficient maps is sufficient for equality of the
corresponding packaged finite-jet operator evaluations. -/
theorem FinitePositivePowerJetData.eval_eq_of_coefficientMap_eq
    (d₁ d₂ : FinitePositivePowerJetData α)
    (A : α → E →L[ℝ] E)
    (h : d₁.coefficientMap = d₂.coefficientMap) :
    d₁.eval A = d₂.eval A := by
  rw [← d₁.coefficientMap_eval_eq A,
    ← d₂.coefficientMap_eval_eq A, h]

/-- Canonical coefficient map of an arbitrary nonempty positive multiplicity
profile after all confluent/binomial adjoin steps. -/
noncomputable def positiveMultiplicityProfileCoefficientMap
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    PositivePowerJetCoefficientMap α :=
  (positiveMultiplicityProfileData value first tail).coefficientMap

/-- Evaluation of the canonical profile coefficient map is exactly evaluation
of the original existentially labelled flattened jet. -/
theorem positiveMultiplicityProfileCoefficientMap_eval_eq_data
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfileCoefficientMap value first tail) A =
      (positiveMultiplicityProfileData value first tail).eval A := by
  exact
    (positiveMultiplicityProfileData value first tail).coefficientMap_eval_eq A

/-- For every compatible profile, the canonical coefficient map evaluates to
the same arbitrary-length mixed operator product. -/
theorem positiveMultiplicityProfileCoefficientMap_eval_eq_product
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hCompatible :
      positiveMultiplicityProfileCompatible value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b)) :
    PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfileCoefficientMap value first tail) A =
      positiveMultiplicityProfileProduct A first tail := by
  calc
    PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfileCoefficientMap value first tail) A =
      (positiveMultiplicityProfileData value first tail).eval A :=
        positiveMultiplicityProfileCoefficientMap_eval_eq_data
          A value first tail
    _ = positiveMultiplicityProfileProduct A first tail :=
      positiveMultiplicityProfileData_eval_eq_product
        A value first tail hCompatible hIdentity

/-- Pairwise scalar distinctness alone identifies the canonical aggregated
coefficient map with the arbitrary-length mixed operator product. -/
theorem positiveMultiplicityProfileCoefficientMap_eval_eq_product_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first tail)
    (hIdentity : ∀ a b : α,
      A a - A b = (value a - value b) • (A a * A b)) :
    PositivePowerJetCoefficientMap.eval
        (positiveMultiplicityProfileCoefficientMap value first tail) A =
      positiveMultiplicityProfileProduct A first tail := by
  exact positiveMultiplicityProfileCoefficientMap_eval_eq_product
    A value first tail
    (positiveMultiplicityProfileCompatible_of_pairwise
      value first tail hPairwise)
    hIdentity

/-- Pointwise pairwise-distinct canonical coefficient-map identity. -/
theorem positiveMultiplicityProfileCoefficientMap_eval_apply_eq_product_apply_of_pairwise
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
        (positiveMultiplicityProfileCoefficientMap value first tail) A x =
      positiveMultiplicityProfileProduct A first tail x := by
  exact DFunLike.congr_fun
    (positiveMultiplicityProfileCoefficientMap_eval_eq_product_of_pairwise
      A value first tail hPairwise hIdentity) x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
