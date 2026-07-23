import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanOptimalRichardsonLogarithmicComplexityLimitL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 300000

/-- A general neighborhood consequence: a real-valued function converging to a
point strictly between two bounds is eventually strictly between those bounds. -/
theorem tendsto_nhds_eventually_strictBetween
    {α : Type*}
    {l : Filter α}
    {f : α → ℝ}
    {a c b : ℝ}
    (h : Tendsto f l (𝓝 c))
    (ha : a < c)
    (hb : c < b) :
    ∀ᶠ x in l, a < f x ∧ f x < b := by
  simpa only [mem_Ioo] using h.eventually (Ioo_mem_nhds ha hb)

private theorem betaZeroOptimalRichardsonContractionFactor_inv_eq_one_add :
    (((323 : ℝ) / 325)⁻¹) = 1 + (2 : ℝ) / 323 := by
  norm_num

/-- The negative logarithm of the actual beta-zero contraction factor is
strictly larger than `1 / 162`. The proof uses the rational lower bound
`2x / (x + 2) < log (1 + x)` at `x = 2 / 323`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_gt_one_div_162 :
    (1 : ℝ) / 162 < -Real.log ((323 : ℝ) / 325) := by
  rw [← Real.log_inv,
    betaZeroOptimalRichardsonContractionFactor_inv_eq_one_add]
  convert Real.lt_log_one_add_of_pos (x := (2 : ℝ) / 323) (by norm_num) using 1 <;>
    norm_num

/-- The negative logarithm of the actual beta-zero contraction factor is
strictly smaller than `1 / 161`. The proof uses `log (1 + x) < x` at
`x = 2 / 323`, followed by the exact rational inequality `2 / 323 < 1 / 161`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_lt_one_div_161 :
    -Real.log ((323 : ℝ) / 325) < (1 : ℝ) / 161 := by
  rw [← Real.log_inv,
    betaZeroOptimalRichardsonContractionFactor_inv_eq_one_add]
  calc
    Real.log (1 + (2 : ℝ) / 323) <
        (1 + (2 : ℝ) / 323) - 1 :=
      Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
    _ < (1 : ℝ) / 161 := by norm_num

/-- Positivity of the negative logarithmic contraction rate, obtained from the
explicit rational lower bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_pos :
    0 < -Real.log ((323 : ℝ) / 325) := by
  exact lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ) / 162)
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_gt_one_div_162

/-- The exact logarithmic complexity constant is strictly larger than `161`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_gt_161 :
    (161 : ℝ) < 1 / (-Real.log ((323 : ℝ) / 325)) := by
  rw [lt_div_iff₀
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_pos]
  nlinarith [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_lt_one_div_161]

/-- The exact logarithmic complexity constant is strictly smaller than `162`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_lt_162 :
    1 / (-Real.log ((323 : ℝ) / 325)) < (162 : ℝ) := by
  rw [div_lt_iff₀
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_pos]
  nlinarith [
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_gt_one_div_162]

/-- Exact rational enclosure of the beta-zero logarithmic iteration-complexity
constant. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_mem_Ioo_161_162 :
    1 / (-Real.log ((323 : ℝ) / 325)) ∈ Set.Ioo (161 : ℝ) 162 :=
  ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_gt_161,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_lt_162⟩

/-- For sufficiently small positive tolerances, the normalized exact
Green--Neumann operator-remainder iteration count lies strictly between the
fully rational constants `161` and `162`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_eventually_mem_Ioo_161_162 :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) < (162 : ℝ) := by
  exact tendsto_nhds_eventually_strictBetween
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_gt_161
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_lt_162

/-- For sufficiently small positive tolerances, the normalized exact
Green--Neumann inverse-defect iteration count lies strictly between the fully
rational constants `161` and `162`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_eventually_mem_Ioo_161_162 :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) < (162 : ℝ) := by
  exact tendsto_nhds_eventually_strictBetween
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_tendsto
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_gt_161
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_lt_162

/-- Structured receipt for the fully rational enclosure of the exact beta-zero
optimal Richardson logarithmic complexity constant and its eventual iteration
ratio consequences. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonComplexityRationalEnclosureL2Receipt :
    Prop where
  negative_log_lower :
    (1 : ℝ) / 162 < -Real.log ((323 : ℝ) / 325)
  negative_log_upper :
    -Real.log ((323 : ℝ) / 325) < (1 : ℝ) / 161
  complexity_constant_enclosure :
    1 / (-Real.log ((323 : ℝ) / 325)) ∈ Set.Ioo (161 : ℝ) 162
  operator_remainder_eventual_enclosure :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) < (162 : ℝ)
  inverse_defect_eventual_enclosure :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (161 : ℝ) <
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) ∧
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount epsilon : ℝ) /
            Real.log (1 / epsilon) < (162 : ℝ)
  claim_boundary : True

/-- The rational-enclosure receipt is inhabited. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonComplexityRationalEnclosureL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardsonComplexityRationalEnclosureL2Receipt := by
  exact
    { negative_log_lower :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_gt_one_div_162
      negative_log_upper :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_negLogContractionFactor_lt_one_div_161
      complexity_constant_enclosure :=
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanOptimalRichardson_logarithmicComplexityConstant_mem_Ioo_161_162
      operator_remainder_eventual_enclosure :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannRemainderEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_eventually_mem_Ioo_161_162
      inverse_defect_eventual_enclosure :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_optimalRichardsonGreenNeumannInverseDefectEndL2_exactStrictLogFloorIterationCount_div_log_oneDiv_eventually_mem_Ioo_161_162
      claim_boundary := trivial }

end
end MathlibAnalytic
end MGAP4D
