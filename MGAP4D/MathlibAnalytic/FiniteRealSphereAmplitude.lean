import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Exact amplitude of a finite real linear form on the unit sphere

The Euclidean length of a finite real coefficient vector bounds the absolute
value of its linear form on the unit sphere. Both signs of the bound are
attained. The zero coefficient case is included: a single coordinate supplies
a unit vector whenever the index type is nonempty.

These statements are independent of any measure, group, or physical model.
-/

namespace MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude

open scoped BigOperators

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι]

/-- The exact unit-sphere amplitude of a finite real linear form. -/
def amplitude (m : ι → ℝ) : ℝ := Real.sqrt (∑ i, m i ^ 2)

/-- A linear-form amplitude is nonnegative. -/
theorem amplitude_nonneg (m : ι → ℝ) : 0 ≤ amplitude m :=
  Real.sqrt_nonneg _

/-- The squared amplitude is the sum of the squared coefficients. -/
theorem amplitude_sq (m : ι → ℝ) : amplitude m ^ 2 = ∑ i, m i ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (m i))

/-- Squared Cauchy-Schwarz for a unit vector. -/
theorem sum_mul_sq_le (m x : ι → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    (∑ i, m i * x i) ^ 2 ≤ ∑ i, m i ^ 2 := by
  simpa only [hx, mul_one] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) m x)

/-- The absolute linear form is bounded by its coefficient amplitude. -/
theorem abs_sum_mul_le_amplitude (m x : ι → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    |∑ i, m i * x i| ≤ amplitude m := by
  exact Real.abs_le_sqrt (sum_mul_sq_le m x hx)

/-- The positive amplitude is attained, including when all coefficients vanish. -/
theorem exists_unit_dot_eq_amplitude [Nonempty ι] (m : ι → ℝ) :
    ∃ x : ι → ℝ, (∑ i, x i ^ 2 = 1) ∧
      (∑ i, m i * x i = amplitude m) := by
  classical
  by_cases hA : amplitude m = 0
  · let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
    let x : ι → ℝ := fun i => if i = i0 then 1 else 0
    have hx : ∑ i, x i ^ 2 = 1 := by
      calc
        (∑ i, x i ^ 2) = ∑ i, if i = i0 then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i = i0 <;> simp [x, h]
        _ = 1 := by simp
    refine ⟨x, hx, ?_⟩
    have hb := abs_sum_mul_le_amplitude m x hx
    rw [hA] at hb
    have hd : (∑ i, m i * x i) = 0 :=
      abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    simpa only [hA] using hd
  · refine ⟨fun i => m i / amplitude m, ?_, ?_⟩
    · calc
        (∑ i, (m i / amplitude m) ^ 2) =
            (∑ i, m i ^ 2) / amplitude m ^ 2 := by
          simp only [div_pow, ← Finset.sum_div]
        _ = 1 := by
          rw [← amplitude_sq m]
          exact div_self (pow_ne_zero 2 hA)
    · calc
        (∑ i, m i * (m i / amplitude m)) =
            (∑ i, m i ^ 2) / amplitude m := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = amplitude m := by
          apply (div_eq_iff hA).2
          simpa only [pow_two] using (amplitude_sq m).symm

/-- The negative amplitude is attained by the negative of a positive maximizer. -/
theorem exists_unit_dot_eq_neg_amplitude [Nonempty ι] (m : ι → ℝ) :
    ∃ x : ι → ℝ, (∑ i, x i ^ 2 = 1) ∧
      (∑ i, m i * x i = -amplitude m) := by
  obtain ⟨x, hx, hmx⟩ := exists_unit_dot_eq_amplitude m
  refine ⟨fun i => -x i, ?_, ?_⟩
  · simpa only [neg_sq] using hx
  · calc
      (∑ i, m i * -x i) = -(∑ i, m i * x i) := by
        simp only [mul_neg, Finset.sum_neg_distrib]
      _ = -amplitude m := by rw [hmx]

end

end MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude

#print axioms MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude.amplitude_nonneg
#print axioms MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude.amplitude_sq
#print axioms MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude.sum_mul_sq_le
#print axioms MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude.abs_sum_mul_le_amplitude
#print axioms MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude.exists_unit_dot_eq_amplitude
#print axioms MGAP4D.MathlibAnalytic.FiniteRealSphereAmplitude.exists_unit_dot_eq_neg_amplitude
