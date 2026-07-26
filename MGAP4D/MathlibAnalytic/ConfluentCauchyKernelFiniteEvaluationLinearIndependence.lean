import MGAP4D.MathlibAnalytic.ContinuousLinearMapRationalFunctionalCalculusPositivePowerJetFaithfulness
import MGAP4D.MathlibAnalytic.SimpleCauchyKernelFiniteEvaluationLinearIndependence
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

/-- Cancelling a positive inverse-power block from a larger positive power. -/
theorem pow_mul_inv_pow_eq_pow_sub
    {K : Type*} [CommGroupWithZero K]
    {x : K} (hx : x ≠ 0) {n m : ℕ} (hnm : n ≤ m) :
    x ^ m * (x⁻¹) ^ n = x ^ (m - n) := by
  have hdecomp : m - n + n = m := Nat.sub_add_cancel hnm
  calc
    x ^ m * (x⁻¹) ^ n = x ^ (m - n + n) * (x⁻¹) ^ n := by rw [hdecomp]
    _ = (x ^ (m - n) * x ^ n) * (x⁻¹) ^ n := by rw [pow_add]
    _ = x ^ (m - n) * (x ^ n * (x⁻¹) ^ n) := by ac_rfl
    _ = x ^ (m - n) * ((x * x⁻¹) ^ n) := by rw [mul_pow]
    _ = x ^ (m - n) := by simp [hx]

/-- The common polynomial denominator for a finite confluent Cauchy family. -/
noncomputable def confluentCauchyCommonDenominatorPolynomial
    [Fintype ι]
    (value : ι → ℝ)
    (orderCap : ℕ) : Polynomial ℝ :=
  ∏ i : ι, (Polynomial.X - Polynomial.C (value i)) ^ orderCap

/-- The common scalar denominator for a finite confluent Cauchy family. -/
def confluentCauchyCommonDenominator
    [Fintype ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (x : ℝ) : ℝ :=
  ∏ i : ι, (x - value i) ^ orderCap

@[simp] theorem confluentCauchyCommonDenominatorPolynomial_eval
    [Fintype ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (x : ℝ) :
    (confluentCauchyCommonDenominatorPolynomial value orderCap).eval x =
      confluentCauchyCommonDenominator value orderCap x := by
  rw [confluentCauchyCommonDenominatorPolynomial, eval_prod]
  simp [confluentCauchyCommonDenominator]

/-- The numerator polynomial obtained after clearing the common denominator from
one node-order Cauchy kernel. -/
noncomputable def confluentCauchyNodeOrderPolynomial
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (i : ι)
    (j : Fin orderCap) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (value i)) ^
      (orderCap - (j.1 + 1)) *
    ∏ l ∈ (Finset.univ : Finset ι).erase i,
      (Polynomial.X - Polynomial.C (value l)) ^ orderCap

@[simp] theorem confluentCauchyNodeOrderPolynomial_eval
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (i : ι)
    (j : Fin orderCap)
    (x : ℝ) :
    (confluentCauchyNodeOrderPolynomial value orderCap i j).eval x =
      (x - value i) ^ (orderCap - (j.1 + 1)) *
        ∏ l ∈ (Finset.univ : Finset ι).erase i,
          (x - value l) ^ orderCap := by
  rw [confluentCauchyNodeOrderPolynomial, eval_mul, eval_pow, eval_prod]
  simp

/-- Clearing the common denominator from one non-pole confluent Cauchy kernel
produces its node-order numerator polynomial. -/
theorem confluentCauchyCommonDenominator_mul_inv_sub_pow
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (x : ℝ)
    (i : ι)
    (j : Fin orderCap)
    (hxi : x ≠ value i) :
    confluentCauchyCommonDenominator value orderCap x *
        ((x - value i)⁻¹ ^ (j.1 + 1)) =
      (confluentCauchyNodeOrderPolynomial value orderCap i j).eval x := by
  rw [confluentCauchyNodeOrderPolynomial_eval]
  unfold confluentCauchyCommonDenominator
  rw [← Finset.mul_prod_erase
    (s := (Finset.univ : Finset ι))
    (f := fun l => (x - value l) ^ orderCap)
    (Finset.mem_univ i)]
  have hnonzero : x - value i ≠ 0 := sub_ne_zero.mpr hxi
  have horder : j.1 + 1 ≤ orderCap := Nat.succ_le_iff.mpr j.2
  calc
    ((x - value i) ^ orderCap *
          ∏ l ∈ (Finset.univ : Finset ι).erase i,
            (x - value l) ^ orderCap) *
        ((x - value i)⁻¹ ^ (j.1 + 1)) =
      ((x - value i) ^ orderCap *
          ((x - value i)⁻¹ ^ (j.1 + 1))) *
        ∏ l ∈ (Finset.univ : Finset ι).erase i,
          (x - value l) ^ orderCap := by ring
    _ = (x - value i) ^ (orderCap - (j.1 + 1)) *
        ∏ l ∈ (Finset.univ : Finset ι).erase i,
          (x - value l) ^ orderCap := by
      rw [pow_mul_inv_pow_eq_pow_sub hnonzero horder]

/-- Every cleared node-order numerator has degree strictly below the total
number of node-order columns. -/
theorem confluentCauchyNodeOrderPolynomial_natDegree_lt
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (hOrderCap : 0 < orderCap)
    (i : ι)
    (j : Fin orderCap) :
    (confluentCauchyNodeOrderPolynomial value orderCap i j).natDegree <
      Fintype.card ι * orderCap := by
  have hFirst :
      ((Polynomial.X - Polynomial.C (value i)) ^
        (orderCap - (j.1 + 1))).natDegree =
          orderCap - (j.1 + 1) := by simp
  have hRest :
      (∏ l ∈ (Finset.univ : Finset ι).erase i,
        (Polynomial.X - Polynomial.C (value l)) ^ orderCap).natDegree =
          (Fintype.card ι - 1) * orderCap := by
    rw [Polynomial.natDegree_prod_of_monic]
    · simp [Finset.card_erase_of_mem]
    · intro l hl
      exact (Polynomial.monic_X_sub_C (value l)).pow orderCap
  have hCardPos : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨i⟩
  have hFirstLt : orderCap - (j.1 + 1) < orderCap := by omega
  have hCardDecomp : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  calc
    (confluentCauchyNodeOrderPolynomial value orderCap i j).natDegree ≤
        ((Polynomial.X - Polynomial.C (value i)) ^
          (orderCap - (j.1 + 1))).natDegree +
        (∏ l ∈ (Finset.univ : Finset ι).erase i,
          (Polynomial.X - Polynomial.C (value l)) ^ orderCap).natDegree := by
      exact Polynomial.natDegree_mul_le
    _ = (orderCap - (j.1 + 1)) +
          (Fintype.card ι - 1) * orderCap := by rw [hFirst, hRest]
    _ < orderCap + (Fintype.card ι - 1) * orderCap := by
      exact Nat.add_lt_add_right hFirstLt _
    _ = ((Fintype.card ι - 1) + 1) * orderCap := by ring
    _ = Fintype.card ι * orderCap := by rw [← hCardDecomp]

/-- The polynomial numerator associated with a finite linear combination of
confluent Cauchy kernels. -/
noncomputable def confluentCauchyNumeratorPolynomial
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (coefficient : ι × Fin orderCap → ℝ) : Polynomial ℝ :=
  ∑ p : ι × Fin orderCap,
    Polynomial.C (coefficient p) *
      confluentCauchyNodeOrderPolynomial value orderCap p.1 p.2

@[simp] theorem confluentCauchyNumeratorPolynomial_eval
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (coefficient : ι × Fin orderCap → ℝ)
    (x : ℝ) :
    (confluentCauchyNumeratorPolynomial value orderCap coefficient).eval x =
      ∑ p : ι × Fin orderCap,
        coefficient p *
          (confluentCauchyNodeOrderPolynomial value orderCap p.1 p.2).eval x := by
  rw [confluentCauchyNumeratorPolynomial, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp

/-- A confluent Cauchy numerator has degree strictly below the total number of
node-order columns. -/
theorem confluentCauchyNumeratorPolynomial_degree_lt
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (hOrderCap : 0 < orderCap)
    (coefficient : ι × Fin orderCap → ℝ) :
    (confluentCauchyNumeratorPolynomial value orderCap coefficient).degree <
      (Fintype.card ι * orderCap : WithBot ℕ) := by
  have hTotalPos : 0 < Fintype.card ι * orderCap :=
    Nat.mul_pos (Fintype.card_pos_iff.mpr inferInstance) hOrderCap
  have hNatDegree :
      (confluentCauchyNumeratorPolynomial value orderCap coefficient).natDegree ≤
        Fintype.card ι * orderCap - 1 := by
    unfold confluentCauchyNumeratorPolynomial
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro p hp
    have hNode := confluentCauchyNodeOrderPolynomial_natDegree_lt
      value orderCap hOrderCap p.1 p.2
    calc
      (Polynomial.C (coefficient p) *
          confluentCauchyNodeOrderPolynomial value orderCap p.1 p.2).natDegree ≤
        (Polynomial.C (coefficient p)).natDegree +
          (confluentCauchyNodeOrderPolynomial value orderCap p.1 p.2).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + (Fintype.card ι * orderCap - 1) := by
        have hNodePred :
            (confluentCauchyNodeOrderPolynomial value orderCap p.1 p.2).natDegree ≤
              Fintype.card ι * orderCap - 1 := by omega
        exact Nat.add_le_add (by simp) hNodePred
      _ = Fintype.card ι * orderCap - 1 := Nat.zero_add _
  by_cases hzero :
      confluentCauchyNumeratorPolynomial value orderCap coefficient = 0
  · rw [hzero, Polynomial.degree_zero]
    simpa using (WithBot.bot_lt_coe (Fintype.card ι * orderCap))
  · rw [Polynomial.degree_eq_natDegree hzero]
    have hPred :
        Fintype.card ι * orderCap - 1 < Fintype.card ι * orderCap := by omega
    exact_mod_cast lt_of_le_of_lt hNatDegree hPred

/-- Equality of two confluent Cauchy combinations on sufficiently many distinct
non-pole samples implies equality of their cleared numerator polynomials. -/
theorem confluentCauchyNumeratorPolynomial_eq_of_eval_eq
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Nonempty ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (hOrderCap : 0 < orderCap)
    (sample : κ → ℝ)
    (hSampleInjective : Function.Injective sample)
    (hCard : Fintype.card κ = Fintype.card ι * orderCap)
    (hNonpole : ∀ k i, sample k ≠ value i)
    (left right : ι × Fin orderCap → ℝ)
    (hEquality :
      (∑ p, left p • fun k =>
        ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1))) =
      ∑ p, right p • fun k =>
        ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1))) :
    confluentCauchyNumeratorPolynomial value orderCap left =
      confluentCauchyNumeratorPolynomial value orderCap right := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (s := (Finset.univ : Finset κ)) hSampleInjective.injOn
  · simpa [hCard] using
      confluentCauchyNumeratorPolynomial_degree_lt value orderCap hOrderCap left
  · simpa [hCard] using
      confluentCauchyNumeratorPolynomial_degree_lt value orderCap hOrderCap right
  · intro k hk
    have hPoint := congrFun hEquality k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hPoint
    simp only [confluentCauchyNumeratorPolynomial_eval]
    calc
      (∑ p : ι × Fin orderCap,
          left p *
            (confluentCauchyNodeOrderPolynomial
              value orderCap p.1 p.2).eval (sample k)) =
        confluentCauchyCommonDenominator value orderCap (sample k) *
          ∑ p : ι × Fin orderCap,
            left p * ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        calc
          left p *
              (confluentCauchyNodeOrderPolynomial
                value orderCap p.1 p.2).eval (sample k) =
            left p *
              (confluentCauchyCommonDenominator value orderCap (sample k) *
                ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1))) := by
              rw [confluentCauchyCommonDenominator_mul_inv_sub_pow
                value orderCap (sample k) p.1 p.2 (hNonpole k p.1)]
          _ = confluentCauchyCommonDenominator value orderCap (sample k) *
              (left p * ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1))) := by ring
      _ = confluentCauchyCommonDenominator value orderCap (sample k) *
          ∑ p : ι × Fin orderCap,
            right p * ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1)) := by rw [hPoint]
      _ = ∑ p : ι × Fin orderCap,
          right p *
            (confluentCauchyNodeOrderPolynomial
              value orderCap p.1 p.2).eval (sample k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        calc
          confluentCauchyCommonDenominator value orderCap (sample k) *
              (right p * ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1))) =
            right p *
              (confluentCauchyCommonDenominator value orderCap (sample k) *
                ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1))) := by ring
          _ = right p *
              (confluentCauchyNodeOrderPolynomial
                value orderCap p.1 p.2).eval (sample k) := by
            rw [confluentCauchyCommonDenominator_mul_inv_sub_pow
              value orderCap (sample k) p.1 p.2 (hNonpole k p.1)]

/-- The common denominator polynomial is nonzero. -/
theorem confluentCauchyCommonDenominatorPolynomial_ne_zero
    [Fintype ι]
    (value : ι → ℝ)
    (orderCap : ℕ) :
    confluentCauchyCommonDenominatorPolynomial value orderCap ≠ 0 := by
  unfold confluentCauchyCommonDenominatorPolynomial
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (value i))

/-- After mapping to rational functions, a cleared node-order numerator equals
the common denominator times the corresponding shifted inverse power. -/
theorem confluentCauchyNodeOrderPolynomial_algebraMap
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (i : ι)
    (j : Fin orderCap) :
    algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (confluentCauchyNodeOrderPolynomial value orderCap i j) =
      algebraMap (Polynomial ℝ) (RatFunc ℝ)
          (confluentCauchyCommonDenominatorPolynomial value orderCap) *
        shiftedInversePowerRatFunc (-value i) j.1 := by
  classical
  let g : RatFunc ℝ := algebraMap (Polynomial ℝ) (RatFunc ℝ)
    (Polynomial.X - Polynomial.C (value i))
  let rest : RatFunc ℝ :=
    ∏ l ∈ (Finset.univ : Finset ι).erase i,
      algebraMap (Polynomial ℝ) (RatFunc ℝ)
        ((Polynomial.X - Polynomial.C (value l)) ^ orderCap)
  have hg : g ≠ 0 := by
    intro hzero
    apply Polynomial.X_sub_C_ne_zero (value i)
    apply FaithfulSMul.algebraMap_injective (Polynomial ℝ) (RatFunc ℝ)
    simpa [g] using hzero
  have horder : j.1 + 1 ≤ orderCap := Nat.succ_le_iff.mpr j.2
  have hpow : g ^ orderCap * (g⁻¹) ^ (j.1 + 1) =
      g ^ (orderCap - (j.1 + 1)) :=
    pow_mul_inv_pow_eq_pow_sub hg horder
  have hShifted :
      shiftedInversePowerRatFunc (-value i) j.1 =
        (g⁻¹) ^ (j.1 + 1) := by
    simp [shiftedInversePowerRatFunc, shiftedLinearPolynomial, g, sub_eq_add_neg]
  rw [confluentCauchyNodeOrderPolynomial,
    confluentCauchyCommonDenominatorPolynomial]
  rw [← Finset.mul_prod_erase
    (s := (Finset.univ : Finset ι))
    (f := fun l => (Polynomial.X - Polynomial.C (value l)) ^ orderCap)
    (Finset.mem_univ i)]
  simp only [map_mul, map_pow, map_prod]
  have hAlgebra :
      g ^ (orderCap - (j.1 + 1)) * rest =
        (g ^ orderCap * rest) * (g⁻¹) ^ (j.1 + 1) := by
    rw [hpow]
    ring
  simpa [g, rest, hShifted] using hAlgebra

/-- Mapping a confluent numerator polynomial to rational functions factors out
the common denominator from the associated inverse-power combination. -/
theorem confluentCauchyNumeratorPolynomial_algebraMap
    [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (coefficient : ι × Fin orderCap → ℝ) :
    algebraMap (Polynomial ℝ) (RatFunc ℝ)
        (confluentCauchyNumeratorPolynomial value orderCap coefficient) =
      algebraMap (Polynomial ℝ) (RatFunc ℝ)
          (confluentCauchyCommonDenominatorPolynomial value orderCap) *
        ∑ p : ι × Fin orderCap,
          coefficient p • shiftedInversePowerRatFunc (-value p.1) p.2.1 := by
  rw [confluentCauchyNumeratorPolynomial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_mul, confluentCauchyNodeOrderPolynomial_algebraMap]
  simp [Algebra.smul_def]
  ring

/-- For equally many distinct nodes-orders and distinct non-pole samples, the
full confluent Cauchy kernel family is linearly independent. -/
theorem confluentCauchyKernel_linearIndependent
    [Fintype ι] [DecidableEq ι]
    [Fintype κ]
    (value : ι → ℝ)
    (orderCap : ℕ)
    (sample : κ → ℝ)
    (hValueInjective : Function.Injective value)
    (hSampleInjective : Function.Injective sample)
    (hCard : Fintype.card κ = Fintype.card ι * orderCap)
    (hNonpole : ∀ k i, sample k ≠ value i) :
    LinearIndependent ℝ
      (fun p : ι × Fin orderCap => fun k : κ =>
        ((sample k - value p.1)⁻¹ ^ (p.2.1 + 1))) := by
  classical
  by_cases hOrderCap : orderCap = 0
  · subst hOrderCap
    rw [Fintype.linearIndependent_iffₛ]
    intro left right hEquality p
    exact Fin.elim0 p.2
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
      letI := hEmpty
      rw [Fintype.linearIndependent_iffₛ]
      intro left right hEquality p
      exact isEmptyElim p.1
  | inr hNonempty =>
      letI := hNonempty
      have hOrderCapPos : 0 < orderCap := Nat.pos_of_ne_zero hOrderCap
      rw [Fintype.linearIndependent_iffₛ]
      intro left right hEquality p
      have hPolynomial := confluentCauchyNumeratorPolynomial_eq_of_eval_eq
        value orderCap hOrderCapPos sample hSampleInjective hCard hNonpole
        left right hEquality
      have hMapped := congrArg
        (algebraMap (Polynomial ℝ) (RatFunc ℝ)) hPolynomial
      rw [confluentCauchyNumeratorPolynomial_algebraMap,
        confluentCauchyNumeratorPolynomial_algebraMap] at hMapped
      have hDenominator :
          algebraMap (Polynomial ℝ) (RatFunc ℝ)
            (confluentCauchyCommonDenominatorPolynomial value orderCap) ≠ 0 := by
        intro hzero
        apply confluentCauchyCommonDenominatorPolynomial_ne_zero value orderCap
        apply FaithfulSMul.algebraMap_injective (Polynomial ℝ) (RatFunc ℝ)
        simpa using hzero
      have hRatFunc :
          (∑ q : ι × Fin orderCap,
              left q • shiftedInversePowerRatFunc (-value q.1) q.2.1) =
            ∑ q : ι × Fin orderCap,
              right q • shiftedInversePowerRatFunc (-value q.1) q.2.1 :=
        mul_left_cancel₀ hDenominator hMapped
      have hNegInjective : Function.Injective (fun i => -value i) := by
        intro i j hneg
        apply hValueInjective
        have h := congrArg Neg.neg hneg
        simpa using h
      have hCoefficients := shiftedInversePowerRatFunc_coefficients_unique
        (fun i => -value i) orderCap hNegInjective
        (fun i j => left (i, j))
        (fun i j => right (i, j))
        (by simpa [Fintype.sum_prod_type] using hRatFunc)
      exact congrFun (congrFun hCoefficients p.1) p.2

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D