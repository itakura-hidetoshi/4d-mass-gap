import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstHaarQuantitativeTopSlopeV5_PZ37ANZ
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOA — fixed-volume right limit of the genuine physical first-mode slope

The domain is the original nonnegative physical coupling, represented by
`NNReal`. The source filter is the punctured right neighborhood of zero.
ANZ's quantitative estimate implies that the absolute normalized slope
error tends to zero and hence that the slope tends to `-1/4`.

The original Wilson action, Haar measure, Gauss-law Hilbert space,
nonnegative top eigenvector, and first physical mode are used unchanged.
Every result fixes a finite `H`; no estimate uniform in `H` is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped Topology NNReal InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- At each fixed finite volume, the absolute error in the actual
physical top/first-mode normalized slope tends to zero from the right. -/
theorem p4Q2PZ37AOA_originalPhysicalTopFirst_normalizedSlopeError_tendsto_zero
    (H : ℕ) :
    Tendsto
      (fun beta : ℝ≥0 =>
        |(inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H 2 (by norm_num) (beta : ℝ) beta.property)
            (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)) / (beta : ℝ) +
          (1 / 4 : ℝ)|)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  let C : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let K : ℝ := 16 * C^2 + 2 * C
  have hcoe : Tendsto (fun beta : ℝ≥0 => (beta : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    simpa only [NNReal.coe_zero] using
      (NNReal.tendsto_coe (m := fun beta : ℝ≥0 => beta) (x := (0 : ℝ≥0))).2
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun beta : ℝ≥0 => beta)
            (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ≥0)))
  have hC : Tendsto (fun beta : ℝ≥0 => C * (beta : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hcoe.const_mul C
  have hK : Tendsto (fun beta : ℝ≥0 => K * (beta : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hcoe.const_mul K
  have hsmall : ∀ᶠ beta : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      C * (beta : ℝ) < (1 / 64 : ℝ) :=
    hC.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 64))
  have hpos : ∀ᶠ beta : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0 < beta :=
    self_mem_nhdsWithin
  have hbound : ∀ᶠ beta : ℝ≥0 in 𝓝[>] (0 : ℝ≥0),
      |(inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H 2 (by norm_num) (beta : ℝ) beta.property)
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)) / (beta : ℝ) +
        (1 / 4 : ℝ)| ≤ K * (beta : ℝ) := by
    filter_upwards [hpos, hsmall] with beta hbeta hlinear
    have hbetaReal : (0 : ℝ) < (beta : ℝ) := by exact_mod_cast hbeta
    exact p4Q2PZ37ANZ_originalPhysicalTopFirst_normalizedSlopeError_le
      H (beta : ℝ) hbetaReal hlinear.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hK
    (Eventually.of_forall fun beta => abs_nonneg _) hbound

/-- The right normalized slope of the original physical Wilson
top/first-mode overlap is `-1/4` at every fixed finite volume. -/
theorem p4Q2PZ37AOA_originalPhysicalTopFirst_normalizedSlope_tendsto_neg_quarter
    (H : ℕ) :
    Tendsto
      (fun beta : ℝ≥0 =>
        (inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H 2 (by norm_num) (beta : ℝ) beta.property)
            (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)) / (beta : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (-(1 / 4 : ℝ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, sub_neg_eq_add] using
    p4Q2PZ37AOA_originalPhysicalTopFirst_normalizedSlopeError_tendsto_zero H

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOA_originalPhysicalTopFirst_normalizedSlopeError_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOA_originalPhysicalTopFirst_normalizedSlope_tendsto_neg_quarter
