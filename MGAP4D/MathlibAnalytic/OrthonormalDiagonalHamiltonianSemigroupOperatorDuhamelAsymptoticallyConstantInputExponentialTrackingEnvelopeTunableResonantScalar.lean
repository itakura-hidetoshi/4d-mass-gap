import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeSharpResonantScalar

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The resonant linear-exponential term admits the sharp envelope at every slower rate
`ν < δ`:
`τ exp (-δ τ) ≤ (1 / (exp 1 * (δ - ν))) exp (-ν τ)`.

The constant is sharp for the fixed target rate `ν`, with equality at
`τ = 1 / (δ - ν)`. No sign assumption on `τ` is needed. -/
theorem mul_exp_tail_le_one_div_exp_one_mul_sub_mul_exp_rate
    (δ ν τ : ℝ)
    (hνδ : ν < δ) :
    τ * Real.exp (-(τ * δ)) ≤
      (1 / (Real.exp 1 * (δ - ν))) * Real.exp (-(τ * ν)) := by
  have hgap : 0 < δ - ν := sub_pos.mpr hνδ
  have hxle :
      (δ - ν) * τ ≤ Real.exp (((δ - ν) * τ) - 1) := by
    simpa using Real.add_one_le_exp (((δ - ν) * τ) - 1)
  have hinvnonneg : 0 ≤ 1 / (δ - ν) := by positivity
  have htau :
      τ ≤ (1 / (Real.exp 1 * (δ - ν))) * Real.exp ((δ - ν) * τ) := by
    calc
      τ = (1 / (δ - ν)) * ((δ - ν) * τ) := by
        field_simp [hgap.ne']
      _ ≤ (1 / (δ - ν)) * Real.exp (((δ - ν) * τ) - 1) :=
        mul_le_mul_of_nonneg_left hxle hinvnonneg
      _ = (1 / (Real.exp 1 * (δ - ν))) * Real.exp ((δ - ν) * τ) := by
        rw [Real.exp_sub]
        field_simp [hgap.ne', Real.exp_ne_zero]
  have hmul :=
    mul_le_mul_of_nonneg_right htau (Real.exp_pos (-(τ * δ))).le
  calc
    τ * Real.exp (-(τ * δ)) ≤
        ((1 / (Real.exp 1 * (δ - ν))) * Real.exp ((δ - ν) * τ)) *
          Real.exp (-(τ * δ)) := hmul
    _ = (1 / (Real.exp 1 * (δ - ν))) * Real.exp (-(τ * ν)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

end

end MathlibAnalytic
end MGAP4D
