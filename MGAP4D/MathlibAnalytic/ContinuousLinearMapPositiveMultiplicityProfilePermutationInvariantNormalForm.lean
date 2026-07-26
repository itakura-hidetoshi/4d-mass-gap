import MGAP4D.MathlibAnalytic.ContinuousLinearMapPairwiseDistinctPositiveMultiplicityProfileConfluentBinomialNormalForm
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

universe u

variable {α E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The positive operator-power factor carried by one multiplicity-profile entry. -/
noncomputable def PositiveMultiplicityProfileEntry.operatorFactor
    (A : α → E →L[ℝ] E)
    (e : PositiveMultiplicityProfileEntry α) : E →L[ℝ] E :=
  (A e.node) ^ (e.order + 1)

/-- Two resolvents commute whenever the two-sided resolvent identity holds and
 their scalar parameters are distinct. -/
theorem commute_of_resolvent_identity
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (a b : α)
    (hne : value a ≠ value b)
    (hIdentity : ∀ x y : α,
      A x - A y = (value x - value y) • (A x * A y)) :
    Commute (A a) (A b) := by
  let delta : ℝ := value a - value b
  have hdelta : delta ≠ 0 := by
    exact sub_ne_zero.mpr hne
  have hsmul :
      delta • (A a * A b) = delta • (A b * A a) := by
    calc
      delta • (A a * A b) = A a - A b := by
        simpa [delta] using (hIdentity a b).symm
      _ = -(A b - A a) := by
        abel
      _ = -((value b - value a) • (A b * A a)) := by
        rw [hIdentity b a]
      _ = delta • (A b * A a) := by
        rw [show value b - value a = -delta by
          dsimp [delta]
          ring]
        simp
  have hcancel := congrArg
    (fun T : E →L[ℝ] E => delta⁻¹ • T) hsmul
  simpa [smul_smul, hdelta] using hcancel

/-- Distinct profile entries carry commuting positive operator-power factors. -/
theorem PositiveMultiplicityProfileEntry.operatorFactor_commute
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (left right : PositiveMultiplicityProfileEntry α)
    (hne : left.ValueDistinct value right)
    (hIdentity : ∀ x y : α,
      A x - A y = (value x - value y) • (A x * A y)) :
    Commute (left.operatorFactor A) (right.operatorFactor A) := by
  exact Commute.pow_pow
    (commute_of_resolvent_identity A value left.node right.node hne hIdentity)
    (left.order + 1) (right.order + 1)

/-- Pairwise scalar-distinct profile entries map to pairwise commuting operator
 power factors. -/
theorem positiveMultiplicityProfileOperatorFactors_pairwise_commute
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (entries : List (PositiveMultiplicityProfileEntry α))
    (hPairwise : entries.Pairwise
      (PositiveMultiplicityProfileEntry.ValueDistinct value))
    (hIdentity : ∀ x y : α,
      A x - A y = (value x - value y) • (A x * A y)) :
    (entries.map (fun e => e.operatorFactor A)).Pairwise Commute := by
  induction entries with
  | nil =>
      simp
  | cons e es ih =>
      cases hPairwise with
      | cons hHead hTail =>
          rw [List.map_cons]
          constructor
          · intro factor hfactor
            rcases List.mem_map.mp hfactor with ⟨e', he', rfl⟩
            exact e.operatorFactor_commute A value e'
              (hHead e' he') hIdentity
          · exact ih hTail

/-- The tail-recursive left-associated profile fold equals the initial operator
 multiplied by the ordinary list product of profile factors. -/
theorem positiveMultiplicityProfileProductFrom_eq_mul_prod
    (A : α → E →L[ℝ] E)
    (T : E →L[ℝ] E)
    (entries : List (PositiveMultiplicityProfileEntry α)) :
    positiveMultiplicityProfileProductFrom A T entries =
      T * (entries.map (fun e => e.operatorFactor A)).prod := by
  induction entries generalizing T with
  | nil =>
      simp [positiveMultiplicityProfileProductFrom]
  | cons e es ih =>
      simp only [positiveMultiplicityProfileProductFrom]
      rw [ih]
      simp [PositiveMultiplicityProfileEntry.operatorFactor, mul_assoc]

/-- A nonempty positive multiplicity profile product is the ordinary list
 product of its positive operator-power factors. -/
theorem positiveMultiplicityProfileProduct_eq_prod
    (A : α → E →L[ℝ] E)
    (first : PositiveMultiplicityProfileEntry α)
    (tail : List (PositiveMultiplicityProfileEntry α)) :
    positiveMultiplicityProfileProduct A first tail =
      ((first :: tail).map (fun e => e.operatorFactor A)).prod := by
  simpa [positiveMultiplicityProfileProduct,
    PositiveMultiplicityProfileEntry.operatorFactor] using
    (positiveMultiplicityProfileProductFrom_eq_mul_prod
      A ((A first.node) ^ (first.order + 1)) tail)

/-- A pairwise scalar-distinct positive multiplicity product is invariant under
 every permutation of the original profile entries. -/
theorem positiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first₁ tail₁)
    (hIdentity : ∀ x y : α,
      A x - A y = (value x - value y) • (A x * A y)) :
    positiveMultiplicityProfileProduct A first₁ tail₁ =
      positiveMultiplicityProfileProduct A first₂ tail₂ := by
  rw [positiveMultiplicityProfileProduct_eq_prod,
    positiveMultiplicityProfileProduct_eq_prod]
  apply (hPerm.map (fun e => e.operatorFactor A)).prod_eq'
  exact positiveMultiplicityProfileOperatorFactors_pairwise_commute
    A value (first₁ :: tail₁) hPairwise hIdentity

/-- Pointwise form of permutation invariance for pairwise-distinct profile
 products. -/
theorem positiveMultiplicityProfileProduct_apply_eq_of_perm_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise :
      positiveMultiplicityProfilePairwiseDistinct value first₁ tail₁)
    (hIdentity : ∀ x y : α,
      A x - A y = (value x - value y) • (A x * A y))
    (x : E) :
    positiveMultiplicityProfileProduct A first₁ tail₁ x =
      positiveMultiplicityProfileProduct A first₂ tail₂ x := by
  exact DFunLike.congr_fun
    (positiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
      A value first₁ first₂ tail₁ tail₂ hPerm hPairwise hIdentity) x

/-- Flattened finite-jet normal forms have the same operator evaluation for two
 pairwise-distinct orderings of the same positive multiplicity profile. -/
theorem positiveMultiplicityProfileData_eval_eq_of_perm_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      positiveMultiplicityProfilePairwiseDistinct value first₁ tail₁)
    (hPairwise₂ :
      positiveMultiplicityProfilePairwiseDistinct value first₂ tail₂)
    (hIdentity : ∀ x y : α,
      A x - A y = (value x - value y) • (A x * A y)) :
    (positiveMultiplicityProfileData value first₁ tail₁).eval A =
      (positiveMultiplicityProfileData value first₂ tail₂).eval A := by
  rw [positiveMultiplicityProfileData_eval_eq_product_of_pairwise
    A value first₁ tail₁ hPairwise₁ hIdentity]
  rw [positiveMultiplicityProfileData_eval_eq_product_of_pairwise
    A value first₂ tail₂ hPairwise₂ hIdentity]
  exact positiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
    A value first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hIdentity

/-- Pointwise permutation invariance of flattened pairwise-distinct profile
 normal forms. -/
theorem positiveMultiplicityProfileData_eval_apply_eq_of_perm_of_pairwise
    (A : α → E →L[ℝ] E)
    (value : α → ℝ)
    (first₁ first₂ : PositiveMultiplicityProfileEntry α)
    (tail₁ tail₂ : List (PositiveMultiplicityProfileEntry α))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      positiveMultiplicityProfilePairwiseDistinct value first₁ tail₁)
    (hPairwise₂ :
      positiveMultiplicityProfilePairwiseDistinct value first₂ tail₂)
    (hIdentity : ∀ x y : α,
      A x - A y = (value x - value y) • (A x * A y))
    (x : E) :
    (positiveMultiplicityProfileData value first₁ tail₁).eval A x =
      (positiveMultiplicityProfileData value first₂ tail₂).eval A x := by
  exact DFunLike.congr_fun
    (positiveMultiplicityProfileData_eval_eq_of_perm_of_pairwise
      A value first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hPairwise₂
        hIdentity) x

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
