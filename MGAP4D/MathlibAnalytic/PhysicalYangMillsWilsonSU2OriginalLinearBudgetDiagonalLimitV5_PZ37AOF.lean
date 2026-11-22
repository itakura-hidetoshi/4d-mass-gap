import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLinearBudgetFirstModeV5_PZ37AOE
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOF — moving-volume first-mode slope with a linear action budget

For the original physical Wilson model, the actual normalized first-mode
overlap tends to -1/4 along every nontrivial filter if the original product
C_H * beta tends to zero and beta is eventually strictly positive. Volumes
may vary arbitrarily: no monotonicity or separate limit of H is assumed.

The explicit coupling beta_H(t) = t / (1 + C_H) has C_H * beta_H(t) <= t.
Its normalized slope error is at most 81*t for 0 < t <= 1/2, independently
of H. Thus t tending to zero with eventual positivity gives a moving-volume
scalar limit at the linear action-budget scale.

The coupling still depends on volume. These scalar limits do not identify
vectors in different Hilbert spaces, construct an infinite-volume state,
or prove a fixed-positive-coupling volume-uniform spectral gap, completed
OS reconstruction, or a four-dimensional continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped Topology NNReal InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A volume-dependent input to the original physical model at the linear
action-budget scale. The original action and state definitions are unchanged. -/
noncomputable def p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta
    (H : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ⟨(t : ℝ) /
      (1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H),
    div_nonneg t.property (by
      have hC :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
      linarith only [hC])⟩

/-- The rescaled input has original action-budget product at most t,
uniformly over all finite volumes and all nonnegative t. -/
theorem p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta_budget_le
    (H : ℕ) (t : ℝ≥0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta H t : ℝ) ≤ (t : ℝ) := by
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hC : 0 ≤ C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hd : 0 < 1 + C := by linarith only [hC]
  change C * ((t : ℝ) / (1 + C)) ≤ (t : ℝ)
  calc
    C * ((t : ℝ) / (1 + C)) = (C * (t : ℝ)) / (1 + C) := by ring
    _ ≤ (t : ℝ) := by
      apply (div_le_iff₀ hd).2
      nlinarith only [t.property]

/-- Under a vanishing original linear budget, the absolute error of the
actual normalized top/first-mode overlap tends to zero along moving volumes. -/
theorem p4Q2PZ37AOF_originalPhysicalTopFirst_linearBudgetSlopeError_tendsto_zero
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ι → ℕ) (beta : ι → ℝ≥0)
    (hbudget : Tendsto
      (fun i =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget (H i) *
          (beta i : ℝ)) l (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ i in l, 0 < beta i) :
    Tendsto
      (fun i =>
        |(inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property)
            (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)) /
          (beta i : ℝ) + (1 / 4 : ℝ)|)
      l (𝓝 (0 : ℝ)) := by
  have hscaled : Tendsto
      (fun i => 81 *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget (H i) *
          (beta i : ℝ))) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hbudget.const_mul (81 : ℝ)
  have hsmall : ∀ᶠ i in l,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget (H i) *
        (beta i : ℝ) < (1 / 2 : ℝ) :=
    hbudget.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hbound : ∀ᶠ i in l,
      |(inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property)
          (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)) /
        (beta i : ℝ) + (1 / 4 : ℝ)| ≤ 81 *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget (H i) *
          (beta i : ℝ)) := by
    filter_upwards [hpos, hsmall] with i hi hsmalli
    have hbetaReal : (0 : ℝ) < (beta i : ℝ) := by exact_mod_cast hi
    simpa only [mul_assoc] using
      p4Q2PZ37AOE_originalPhysicalTopFirst_normalizedSlopeError_linearBudget
        (H i) (beta i : ℝ) hbetaReal hsmalli.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscaled
    (Eventually.of_forall fun i => abs_nonneg _) hbound

/-- The actual scalar slope tends to -1/4 under a vanishing original
linear budget, with arbitrary finite volumes and eventual positive coupling. -/
theorem p4Q2PZ37AOF_originalPhysicalTopFirst_linearBudgetSlope_tendsto_neg_quarter
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ι → ℕ) (beta : ι → ℝ≥0)
    (hbudget : Tendsto
      (fun i =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget (H i) *
          (beta i : ℝ)) l (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ i in l, 0 < beta i) :
    Tendsto
      (fun i =>
        (inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              (H i) 2 (by norm_num) (beta i : ℝ) (beta i).property)
            (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)) /
          (beta i : ℝ))
      l (𝓝 (-(1 / 4 : ℝ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, sub_neg_eq_add] using
    p4Q2PZ37AOF_originalPhysicalTopFirst_linearBudgetSlopeError_tendsto_zero
      l H beta hbudget hpos

/-- The genuine slope at the linear-budget rescaled input has error at
most 81*t on an explicit t-window independent of the finite volume. -/
theorem p4Q2PZ37AOF_originalPhysicalTopFirst_linearRescaledSlopeError_le
    (H : ℕ) (t : ℝ≥0) (htpos : 0 < t)
    (htsmall : (t : ℝ) ≤ (1 / 2 : ℝ)) :
    |(inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num)
          (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta H t : ℝ)
          (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta H t).property)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)) /
      (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta H t : ℝ) +
      (1 / 4 : ℝ)| ≤ 81 * (t : ℝ) := by
  have hC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hd : 0 < 1 +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
    linarith only [hC]
  have htReal : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have hbetaReal : (0 : ℝ) <
      (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta H t : ℝ) :=
    div_pos htReal hd
  have hbudget := p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta_budget_le H t
  have hbound := p4Q2PZ37AOE_originalPhysicalTopFirst_normalizedSlopeError_linearBudget
    H (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta H t : ℝ)
    hbetaReal (hbudget.trans htsmall)
  have hupper :
      81 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta H t : ℝ) ≤
      81 * (t : ℝ) := by
    nlinarith only [hbudget]
  exact hbound.trans hupper

/-- The explicit linear-budget rescaling yields the same scalar slope
limit along arbitrary moving volumes as the positive parameter tends to zero. -/
theorem p4Q2PZ37AOF_originalPhysicalTopFirst_linearRescaledSlope_tendsto_neg_quarter
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ι → ℕ) (t : ι → ℝ≥0)
    (ht : Tendsto t l (𝓝 (0 : ℝ≥0)))
    (hpos : ∀ᶠ i in l, 0 < t i) :
    Tendsto
      (fun i =>
        (inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              (H i) 2 (by norm_num)
              (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i) : ℝ)
              (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i)).property)
            (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)) /
          (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i) : ℝ))
      l (𝓝 (-(1 / 4 : ℝ))) := by
  have hcoe : Tendsto (fun i => (t i : ℝ)) l (𝓝 (0 : ℝ)) := by
    simpa only [NNReal.coe_zero] using
      (NNReal.tendsto_coe (m := t) (x := (0 : ℝ≥0))).2 ht
  have hbudget : Tendsto
      (fun i =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget (H i) *
          (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i) : ℝ))
      l (𝓝 (0 : ℝ)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hcoe
      (Eventually.of_forall fun i => mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg (H i))
        (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i)).property)
      (Eventually.of_forall fun i =>
        p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta_budget_le (H i) (t i))
  have hbetaPos : ∀ᶠ i in l,
      0 < p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i) := by
    filter_upwards [hpos] with i hi
    have hC :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg (H i)
    have hd : 0 < 1 +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget (H i) := by
      linarith only [hC]
    have htReal : (0 : ℝ) < (t i : ℝ) := by exact_mod_cast hi
    have hbReal : (0 : ℝ) <
        (p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i) : ℝ) :=
      div_pos htReal hd
    exact_mod_cast hbReal
  exact p4Q2PZ37AOF_originalPhysicalTopFirst_linearBudgetSlope_tendsto_neg_quarter
    l H (fun i => p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta (H i) (t i))
    hbudget hbetaPos

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOF_originalPhysicalLinearBudgetRescaledBeta_budget_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOF_originalPhysicalTopFirst_linearBudgetSlopeError_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOF_originalPhysicalTopFirst_linearBudgetSlope_tendsto_neg_quarter
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOF_originalPhysicalTopFirst_linearRescaledSlopeError_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOF_originalPhysicalTopFirst_linearRescaledSlope_tendsto_neg_quarter
