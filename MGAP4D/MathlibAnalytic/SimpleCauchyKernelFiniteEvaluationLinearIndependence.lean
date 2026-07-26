import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set Polynomial
open scoped BigOperators Polynomial

namespace ContinuousLinearMap

universe u v

variable {ι : Type u} {κ : Type v}

/-- The polynomial obtained by deleting one linear node factor from the common
simple-pole denominator. -/
noncomputable def simpleCauchyNodePolynomial
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (i : ι) : Polynomial ℝ :=
  ∏ j ∈ (Finset.univ : Finset ι).erase i,
    (Polynomial.X - Polynomial.C (value j))

@[simp] theorem simpleCauchyNodePolynomial_eval
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (i : ι)
    (x : ℝ) :
    (simpleCauchyNodePolynomial value i).eval x =
      ∏ j ∈ (Finset.univ : Finset ι).erase i, (x - value j) := by
  rw [simpleCauchyNodePolynomial, eval_prod]
  simp

/-- Every deleted-factor node polynomial has degree exactly one less than the
number of nodes. -/
theorem simpleCauchyNodePolynomial_natDegree
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (i : ι) :
    (simpleCauchyNodePolynomial value i).natDegree =
      Fintype.card ι - 1 := by
  rw [simpleCauchyNodePolynomial,
    Polynomial.natDegree_prod_of_monic]
  · simp
  · intro j hj
    exact Polynomial.monic_X_sub_C (value j)

/-- A deleted-factor node polynomial vanishes at every other node. -/
theorem simpleCauchyNodePolynomial_eval_other
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    {i j : ι}
    (hij : i ≠ j) :
    (simpleCauchyNodePolynomial value i).eval (value j) = 0 := by
  rw [simpleCauchyNodePolynomial_eval]
  apply Finset.prod_eq_zero
  · exact Finset.mem_erase.mpr
      ⟨hij.symm, Finset.mem_univ j⟩
  · simp

/-- At its retained node, the deleted-factor node polynomial is nonzero when
node values are injective. -/
theorem simpleCauchyNodePolynomial_eval_self_ne_zero
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (hValueInjective : Function.Injective value)
    (i : ι) :
    (simpleCauchyNodePolynomial value i).eval (value i) ≠ 0 := by
  rw [simpleCauchyNodePolynomial_eval,
    Finset.prod_ne_zero_iff]
  intro j hj
  rcases Finset.mem_erase.mp hj with ⟨hji, _⟩
  exact sub_ne_zero.mpr fun hvalue =>
    hji (hValueInjective hvalue.symm)

/-- The common scalar denominator over all simple-pole nodes. -/
def simpleCauchyCommonDenominator
    [Fintype ι]
    (value : ι → ℝ)
    (x : ℝ) : ℝ :=
  ∏ i : ι, (x - value i)

/-- Multiplying one simple Cauchy kernel by the common denominator gives the
corresponding deleted-factor polynomial evaluation. -/
theorem simpleCauchyCommonDenominator_mul_inv_sub
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (x : ℝ)
    (i : ι)
    (hxi : x ≠ value i) :
    simpleCauchyCommonDenominator value x * (x - value i)⁻¹ =
      (simpleCauchyNodePolynomial value i).eval x := by
  rw [simpleCauchyNodePolynomial_eval]
  unfold simpleCauchyCommonDenominator
  rw [← Finset.mul_prod_erase
    (s := (Finset.univ : Finset ι))
    (f := fun j => x - value j)
    (Finset.mem_univ i)]
  field_simp [sub_ne_zero.mpr hxi]

/-- The polynomial numerator associated with a finite linear combination of
simple Cauchy kernels. -/
noncomputable def simpleCauchyNumeratorPolynomial
    [Fintype ι] [DecidableEq ι]
    (value coefficient : ι → ℝ) : Polynomial ℝ :=
  ∑ i : ι,
    Polynomial.C (coefficient i) * simpleCauchyNodePolynomial value i

@[simp] theorem simpleCauchyNumeratorPolynomial_eval
    [Fintype ι] [DecidableEq ι]
    (value coefficient : ι → ℝ)
    (x : ℝ) :
    (simpleCauchyNumeratorPolynomial value coefficient).eval x =
      ∑ i : ι,
        coefficient i * (simpleCauchyNodePolynomial value i).eval x := by
  rw [simpleCauchyNumeratorPolynomial, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- A simple Cauchy numerator has degree strictly below the number of nodes. -/
theorem simpleCauchyNumeratorPolynomial_degree_lt_card
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (value coefficient : ι → ℝ) :
    (simpleCauchyNumeratorPolynomial value coefficient).degree <
      (Fintype.card ι : WithBot ℕ) := by
  have hNatDegree :
      (simpleCauchyNumeratorPolynomial value coefficient).natDegree ≤
        Fintype.card ι - 1 := by
    unfold simpleCauchyNumeratorPolynomial
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    calc
      (Polynomial.C (coefficient i) *
          simpleCauchyNodePolynomial value i).natDegree ≤
          (Polynomial.C (coefficient i)).natDegree +
            (simpleCauchyNodePolynomial value i).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + (Fintype.card ι - 1) := by
        exact Nat.add_le_add (by simp)
          (le_of_eq (simpleCauchyNodePolynomial_natDegree value i))
      _ = Fintype.card ι - 1 := Nat.zero_add _
  by_cases hzero : simpleCauchyNumeratorPolynomial value coefficient = 0
  · simp [hzero]
  · rw [Polynomial.degree_eq_natDegree hzero]
    have hCardPos : 0 < Fintype.card ι :=
      Fintype.card_pos_iff.mpr inferInstance
    have hPred : Fintype.card ι - 1 < Fintype.card ι := by
      omega
    exact_mod_cast lt_of_le_of_lt hNatDegree hPred

/-- Equality of two simple Cauchy kernel combinations on sufficiently many
injectively indexed non-pole samples implies equality of their numerator
polynomials. -/
theorem simpleCauchyNumeratorPolynomial_eq_of_eval_eq
    [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    (value : ι → ℝ)
    (sample : κ → ℝ)
    (hSampleInjective : Function.Injective sample)
    (hCard : Fintype.card κ = Fintype.card ι)
    (hNonpole : ∀ k i, sample k ≠ value i)
    (left right : ι → ℝ)
    (hEquality :
      (∑ i, left i • fun k => (sample k - value i)⁻¹) =
        ∑ i, right i • fun k => (sample k - value i)⁻¹) :
    simpleCauchyNumeratorPolynomial value left =
      simpleCauchyNumeratorPolynomial value right := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
      letI := hEmpty
      simp [simpleCauchyNumeratorPolynomial]
  | inr hNonempty =>
      letI := hNonempty
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
        (s := (Finset.univ : Finset κ))
        hSampleInjective.injOn
      · simpa [hCard] using
          simpleCauchyNumeratorPolynomial_degree_lt_card value left
      · simpa [hCard] using
          simpleCauchyNumeratorPolynomial_degree_lt_card value right
      · intro k hk
        have hPoint := congrFun hEquality k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hPoint
        simp only [simpleCauchyNumeratorPolynomial_eval]
        calc
          (∑ i : ι,
              left i * (simpleCauchyNodePolynomial value i).eval (sample k)) =
              simpleCauchyCommonDenominator value (sample k) *
                ∑ i : ι, left i * (sample k - value i)⁻¹ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            calc
              left i * (simpleCauchyNodePolynomial value i).eval (sample k) =
                  left i *
                    (simpleCauchyCommonDenominator value (sample k) *
                      (sample k - value i)⁻¹) := by
                rw [simpleCauchyCommonDenominator_mul_inv_sub
                  value (sample k) i (hNonpole k i)]
              _ = simpleCauchyCommonDenominator value (sample k) *
                    (left i * (sample k - value i)⁻¹) := by ring
          _ = simpleCauchyCommonDenominator value (sample k) *
                ∑ i : ι, right i * (sample k - value i)⁻¹ := by
            rw [hPoint]
          _ = ∑ i : ι,
              right i * (simpleCauchyNodePolynomial value i).eval (sample k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            calc
              simpleCauchyCommonDenominator value (sample k) *
                    (right i * (sample k - value i)⁻¹) =
                  right i *
                    (simpleCauchyCommonDenominator value (sample k) *
                      (sample k - value i)⁻¹) := by ring
              _ = right i *
                    (simpleCauchyNodePolynomial value i).eval (sample k) := by
                rw [simpleCauchyCommonDenominator_mul_inv_sub
                  value (sample k) i (hNonpole k i)]

/-- For equally many distinct nodes and non-pole distinct samples, the ordinary
Cauchy kernel columns are linearly independent.  This is the simple-pole base
case for confluent Cauchy spectral separation. -/
theorem simpleCauchyKernel_linearIndependent
    [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    (value : ι → ℝ)
    (sample : κ → ℝ)
    (hValueInjective : Function.Injective value)
    (hSampleInjective : Function.Injective sample)
    (hCard : Fintype.card κ = Fintype.card ι)
    (hNonpole : ∀ k i, sample k ≠ value i) :
    LinearIndependent ℝ
      (fun i : ι => fun k : κ => (sample k - value i)⁻¹) := by
  classical
  rw [Fintype.linearIndependent_iffₛ]
  intro left right hEquality i
  have hPolynomial := simpleCauchyNumeratorPolynomial_eq_of_eval_eq
    value sample hSampleInjective hCard hNonpole left right hEquality
  have hEval := congrArg
    (Polynomial.eval (value i)) hPolynomial
  simp only [simpleCauchyNumeratorPolynomial_eval] at hEval
  have hLeft :
      (∑ j : ι,
          left j * (simpleCauchyNodePolynomial value j).eval (value i)) =
        left i * (simpleCauchyNodePolynomial value i).eval (value i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [simpleCauchyNodePolynomial_eval_other value hji, mul_zero]
    · simp
  have hRight :
      (∑ j : ι,
          right j * (simpleCauchyNodePolynomial value j).eval (value i)) =
        right i * (simpleCauchyNodePolynomial value i).eval (value i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [simpleCauchyNodePolynomial_eval_other value hji, mul_zero]
    · simp
  rw [hLeft, hRight] at hEval
  exact mul_right_cancel₀
    (simpleCauchyNodePolynomial_eval_self_ne_zero
      value hValueInjective i) hEval

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
