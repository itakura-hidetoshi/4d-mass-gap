import MGAP4D.MathlibAnalytic.RealL2ConditionalIndependentPairVariance

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

#check realProbabilityIndependentPair_lintegral_sq_sub_eq_two_mul_evariance
#check realL2_conditionalIndependentPair_norm_sq_eq_two_mul_lintegral_evariance

-- The same-fiber probability law is used twice; a constant has zero pair energy.
example {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (c : ℝ) :
    (∫⁻ _uv : α × α, ENNReal.ofReal ((c - c) ^ 2) ∂μ.prod μ) = 0 := by
  calc
    (∫⁻ _uv : α × α, ENNReal.ofReal ((c - c) ^ 2) ∂μ.prod μ) =
        2 * evariance (fun _ : α => c) μ :=
      realProbabilityIndependentPair_lintegral_sq_sub_eq_two_mul_evariance
        μ (fun _ : α => c) (memLp_const c)
    _ = 0 := by simp

-- Outer extraction of the exact normalization has no extra measurability premise.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (V : α → ℝ≥0∞) :
    (∫⁻ a, (2 : ℝ≥0∞) * V a ∂μ) = 2 * ∫⁻ a, V a ∂μ :=
  lintegral_const_mul' 2 V (by simp)

-- Lp is a bundled subgroup coerced to a subtype; qualify the namespace.
example {α : Type*} [MeasurableSpace α] (μ : Measure α) (L : Lp ℝ 2 μ)
    (G : α → ℝ) (hRep : (fun a => L a) =ᵐ[μ] G) : MemLp G 2 μ :=
  (memLp_congr_ae hRep).mp (_root_.MeasureTheory.Lp.memLp L)

end MGAP4D.MathlibAnalytic
