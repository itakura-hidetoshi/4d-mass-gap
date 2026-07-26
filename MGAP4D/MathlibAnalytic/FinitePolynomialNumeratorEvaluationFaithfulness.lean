import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set Polynomial
open scoped BigOperators Polynomial

namespace ContinuousLinearMap

universe u v w

variable {ι : Type u} {κ : Type v} {M : Type w}
variable [Fintype ι] [DecidableEq ι] [Fintype κ]
variable [AddCommGroup M] [Module ℝ M]

/-- A finite family of scalar sample columns is certified by polynomial
numerators when every finite coefficient combination has a uniformly bounded
numerator degree, sample evaluation is obtained by one common scalar weight,
and equality of numerator polynomials transports back to equality in a
symbolic target family. -/
structure FinitePolynomialNumeratorEvaluationCertificate
    (symbolic : ι → M)
    (column : ι → κ → ℝ)
    (sample : κ → ℝ) where
  numerator : ι → Polynomial ℝ
  weight : κ → ℝ
  numeratorCombinationDegree_lt_card :
    ∀ coefficient : ι → ℝ,
      (∑ i : ι,
        Polynomial.C (coefficient i) * numerator i).degree <
        (Fintype.card κ : WithBot ℕ)
  numeratorCombination_eval :
    ∀ (coefficient : ι → ℝ) (k : κ),
      (∑ i : ι,
        Polynomial.C (coefficient i) * numerator i).eval (sample k) =
        weight k * ∑ i : ι, coefficient i * column i k
  symbolicCombination_eq_of_numeratorCombination_eq :
    ∀ left right : ι → ℝ,
      (∑ i : ι, Polynomial.C (left i) * numerator i) =
          ∑ i : ι, Polynomial.C (right i) * numerator i →
        (∑ i : ι, left i • symbolic i) =
          ∑ i : ι, right i • symbolic i

/-- Distinct sufficiently numerous samples transport symbolic linear
independence to the scalar sample columns through a polynomial-numerator
certificate.  This isolates the root-counting part of finite Cauchy and
confluent Cauchy faithfulness from the family-specific denominator algebra. -/
theorem FinitePolynomialNumeratorEvaluationCertificate.column_linearIndependent
    {symbolic : ι → M}
    {column : ι → κ → ℝ}
    {sample : κ → ℝ}
    (D : FinitePolynomialNumeratorEvaluationCertificate
      symbolic column sample)
    (hSampleInjective : Function.Injective sample)
    (hSymbolic : LinearIndependent ℝ symbolic) :
    LinearIndependent ℝ column := by
  classical
  rw [Fintype.linearIndependent_iffₛ]
  intro left right hColumns i
  have hNumerator :
      (∑ j : ι, Polynomial.C (left j) * D.numerator j) =
        ∑ j : ι, Polynomial.C (right j) * D.numerator j := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (s := (Finset.univ : Finset κ))
      hSampleInjective.injOn
    · exact D.numeratorCombinationDegree_lt_card left
    · exact D.numeratorCombinationDegree_lt_card right
    · intro k hk
      rw [D.numeratorCombination_eval left k,
        D.numeratorCombination_eval right k]
      have hPoint := congrFun hColumns k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hPoint
      rw [hPoint]
  have hSymbolicEquality :=
    D.symbolicCombination_eq_of_numeratorCombination_eq
      left right hNumerator
  rw [Fintype.linearIndependent_iffₛ] at hSymbolic
  exact hSymbolic left right hSymbolicEquality i

/-- Injectivity of the finite sample synthesis map is the equivalent linear-map
form of the transported column independence. -/
theorem FinitePolynomialNumeratorEvaluationCertificate.column_synthesis_injective
    {symbolic : ι → M}
    {column : ι → κ → ℝ}
    {sample : κ → ℝ}
    (D : FinitePolynomialNumeratorEvaluationCertificate
      symbolic column sample)
    (hSampleInjective : Function.Injective sample)
    (hSymbolic : LinearIndependent ℝ symbolic) :
    Function.Injective (Finsupp.linearCombination ℝ column) :=
  (D.column_linearIndependent hSampleInjective hSymbolic).finsuppLinearCombination_injective

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
