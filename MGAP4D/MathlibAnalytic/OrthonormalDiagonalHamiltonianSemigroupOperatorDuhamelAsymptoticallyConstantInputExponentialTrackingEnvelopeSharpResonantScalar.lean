import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeScalar

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The resonant linear-exponential term has the sharp half-rate envelope
`τ exp (-δ τ) ≤ (2 / (exp 1 * δ)) exp (-(δ / 2) τ)`.

The constant is sharp for this fixed half-rate because equality occurs at
`τ = 2 / δ`. -/
theorem mul_exp_tail_le_two_div_exp_one_mul_mul_exp_half_rate
    (δ τ : ℝ)
    (hδpos : 0 < δ) :
    τ * Real.exp (-(τ * δ)) ≤
      (2 / (Real.exp 1 * δ)) * Real.exp (-(τ * (δ / 2))) := by
  have hxle :
      (δ / 2) * τ ≤ Real.exp (((δ / 2) * τ) - 1) := by
    simpa using Real.add_one_le_exp (((δ / 2) * τ) - 1)
  have hinvnonneg : 0 ≤ 1 / (δ / 2) := by positivity
  have htau :
      τ ≤ (2 / (Real.exp 1 * δ)) * Real.exp ((δ / 2) * τ) := by
    calc
      τ = (1 / (δ / 2)) * ((δ / 2) * τ) := by
        field_simp [hδpos.ne']
      _ ≤ (1 / (δ / 2)) * Real.exp (((δ / 2) * τ) - 1) :=
        mul_le_mul_of_nonneg_left hxle hinvnonneg
      _ = (2 / (Real.exp 1 * δ)) * Real.exp ((δ / 2) * τ) := by
        rw [Real.exp_sub]
        field_simp [hδpos.ne', Real.exp_ne_zero]
  have hmul :=
    mul_le_mul_of_nonneg_right htau (Real.exp_pos (-(τ * δ))).le
  calc
    τ * Real.exp (-(τ * δ)) ≤
        ((2 / (Real.exp 1 * δ)) * Real.exp ((δ / 2) * τ)) *
          Real.exp (-(τ * δ)) := hmul
    _ = (2 / (Real.exp 1 * δ)) * Real.exp (-(τ * (δ / 2))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

end

end MathlibAnalytic
end MGAP4D
