import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingRate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The non-resonant exponential difference quotient is controlled by the slower
of the two rates, with the spectral-separation constant `|δ - μ|⁻¹`. -/
theorem exp_tail_difference_quotient_mul_le_single_rate
    (δ μ C τ : ℝ)
    (hδμ : δ ≠ μ)
    (hC : 0 ≤ C) :
    ((Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ)) * C ≤
      (C / |δ - μ|) * Real.exp (-(τ * min δ μ)) := by
  rcases lt_or_gt_of_ne hδμ with hδltμ | hμltδ
  · have hdenpos : 0 < μ - δ := sub_pos.mpr hδltμ
    have hdenne : μ - δ ≠ 0 := ne_of_gt hdenpos
    have hrewrite :
        (Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ) =
          (Real.exp (-(τ * δ)) - Real.exp (-(τ * μ))) / (μ - δ) := by
      field_simp [sub_ne_zero.mpr hδμ, hdenne]
      ring
    have hquot :
        (Real.exp (-(τ * δ)) - Real.exp (-(τ * μ))) / (μ - δ) ≤
          Real.exp (-(τ * δ)) / (μ - δ) := by
      apply (div_le_div_iff₀ hdenpos hdenpos).2
      nlinarith [Real.exp_pos (-(τ * μ))]
    calc
      ((Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ)) * C =
          ((Real.exp (-(τ * δ)) - Real.exp (-(τ * μ))) / (μ - δ)) * C := by
            rw [hrewrite]
      _ ≤ (Real.exp (-(τ * δ)) / (μ - δ)) * C :=
        mul_le_mul_of_nonneg_right hquot hC
      _ = (C / |δ - μ|) * Real.exp (-(τ * min δ μ)) := by
        rw [min_eq_left hδltμ.le, abs_of_neg (sub_neg.mpr hδltμ)]
        ring
  · have hdenpos : 0 < δ - μ := sub_pos.mpr hμltδ
    have hquot :
        (Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ) ≤
          Real.exp (-(τ * μ)) / (δ - μ) := by
      apply (div_le_div_iff₀ hdenpos hdenpos).2
      nlinarith [Real.exp_pos (-(τ * δ))]
    calc
      ((Real.exp (-(τ * μ)) - Real.exp (-(τ * δ))) / (δ - μ)) * C ≤
          (Real.exp (-(τ * μ)) / (δ - μ)) * C :=
        mul_le_mul_of_nonneg_right hquot hC
      _ = (C / |δ - μ|) * Real.exp (-(τ * min δ μ)) := by
        rw [min_eq_right hμltδ.le, abs_of_pos hdenpos]
        ring

/-- The resonant linear-exponential term admits the elementary half-rate envelope
`τ exp (-δ τ) ≤ (2 / δ) exp (-(δ / 2) τ)`. -/
theorem mul_exp_tail_le_two_div_mul_exp_half_rate
    (δ τ : ℝ)
    (hδpos : 0 < δ)
    (hτ : 0 ≤ τ) :
    τ * Real.exp (-(τ * δ)) ≤
      (2 / δ) * Real.exp (-(τ * (δ / 2))) := by
  have hhalfpos : 0 < δ / 2 := by linarith
  have hxle : (δ / 2) * τ ≤ Real.exp ((δ / 2) * τ) := by
    calc
      (δ / 2) * τ ≤ (δ / 2) * τ + 1 := by linarith
      _ ≤ Real.exp ((δ / 2) * τ) := Real.add_one_le_exp _
  have hinvnonneg : 0 ≤ 1 / (δ / 2) := by positivity
  have htau : τ ≤ (2 / δ) * Real.exp ((δ / 2) * τ) := by
    calc
      τ = (1 / (δ / 2)) * ((δ / 2) * τ) := by
        field_simp [hδpos.ne']
      _ ≤ (1 / (δ / 2)) * Real.exp ((δ / 2) * τ) :=
        mul_le_mul_of_nonneg_left hxle hinvnonneg
      _ = (2 / δ) * Real.exp ((δ / 2) * τ) := by
        field_simp [hδpos.ne']
  have hmul :=
    mul_le_mul_of_nonneg_right htau (Real.exp_pos (-(τ * δ))).le
  calc
    τ * Real.exp (-(τ * δ)) ≤
        ((2 / δ) * Real.exp ((δ / 2) * τ)) * Real.exp (-(τ * δ)) := hmul
    _ = (2 / δ) * Real.exp (-(τ * (δ / 2))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

end

end MathlibAnalytic
end MGAP4D
