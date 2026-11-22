import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstHaarRightSlopeLimitV5_PZ37AOA
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOB — volume-dependent rescaling of the genuine first-mode slope

For the original action budget C_H, evaluate the original physical Wilson
top/first Gauss-law overlap at beta_H(t) = t / (1 + C_H)^2.
The original ANZ remainder gives an error at most 16*t for every finite H
and every 0 < t <= 1/16.  The constant and the t-window are independent of H.

The physical coupling beta_H(t) still depends on H.  No fixed positive
physical-coupling window uniform in volume is obtained.  No identification
of Hilbert spaces at different volumes, infinite-volume state, completed
OS reconstruction, or four-dimensional continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped Topology NNReal InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- An explicitly volume-dependent coupling in the original nonnegative
physical parameter domain.  This only chooses an input to the original model. -/
noncomputable def p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta
    (H : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ⟨(t : ℝ) /
      (1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H)^2,
    div_nonneg t.property (sq_nonneg _)⟩

/-- After the explicit volume-dependent coupling substitution, the genuine
normalized overlap has a quantitative error bound independent of H. -/
theorem p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlopeError_le
    (H : ℕ) (t : ℝ≥0) (htpos : 0 < t)
    (htsmall : (t : ℝ) ≤ (1 / 16 : ℝ)) :
    |(inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num)
          (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta H t : ℝ)
          (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta H t).property)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)) /
      (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta H t : ℝ) +
      (1 / 4 : ℝ)| ≤ 16 * (t : ℝ) := by
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let d : ℝ := 1 + C
  let beta : ℝ≥0 := p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta H t
  have hC : 0 ≤ C := by
    dsimp [C, periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget]
    positivity
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hdsq : 0 < d^2 := by positivity
  have htReal : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have hbetaReal : (0 : ℝ) < (beta : ℝ) := by
    change 0 < (t : ℝ) / d^2
    exact div_pos htReal hdsq
  have hCfour : 4 * C ≤ d^2 := by
    dsimp [d]
    nlinarith [sq_nonneg (C - 1)]
  have hK : 16 * C^2 + 2 * C ≤ 16 * d^2 := by
    dsimp [d]
    nlinarith
  have hlinear : C * (beta : ℝ) ≤ (1 / 64 : ℝ) := by
    have hratio : C * (beta : ℝ) ≤ (t : ℝ) / 4 := by
      change C * ((t : ℝ) / d^2) ≤ (t : ℝ) / 4
      calc
        C * ((t : ℝ) / d^2) = (C * (t : ℝ)) / d^2 := by ring
        _ ≤ (t : ℝ) / 4 := by
          apply (div_le_iff₀ hdsq).2
          have hscaled := mul_le_mul_of_nonneg_right hCfour t.property
          nlinarith
    linarith
  have hupper : (16 * C^2 + 2 * C) * (beta : ℝ) ≤ 16 * (t : ℝ) := by
    change (16 * C^2 + 2 * C) * ((t : ℝ) / d^2) ≤ 16 * (t : ℝ)
    calc
      (16 * C^2 + 2 * C) * ((t : ℝ) / d^2) =
          ((16 * C^2 + 2 * C) * (t : ℝ)) / d^2 := by ring
      _ ≤ 16 * (t : ℝ) := by
        apply (div_le_iff₀ hdsq).2
        have hscaled := mul_le_mul_of_nonneg_right hK t.property
        nlinarith
  have hbound := p4Q2PZ37ANZ_originalPhysicalTopFirst_normalizedSlopeError_le
    H (beta : ℝ) hbetaReal hlinear
  exact hbound.trans hupper

/-- Along every nontrivial filter, arbitrary changes of finite volume are
allowed when the rescaled coupling tends to zero and is eventually positive. -/
theorem p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlopeError_tendsto_zero
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ι → ℕ) (t : ι → ℝ≥0)
    (ht : Tendsto t l (𝓝 (0 : ℝ≥0)))
    (hpos : ∀ᶠ i in l, 0 < t i) :
    Tendsto
      (fun i =>
        |(inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              (H i) 2 (by norm_num)
              (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i) : ℝ)
              (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i)).property)
            (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)) /
          (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i) : ℝ) +
          (1 / 4 : ℝ)|)
      l (𝓝 (0 : ℝ)) := by
  have hcoe : Tendsto (fun i => (t i : ℝ)) l (𝓝 (0 : ℝ)) := by
    simpa only [NNReal.coe_zero] using
      (NNReal.tendsto_coe (m := t) (x := (0 : ℝ≥0))).2 ht
  have hscaled : Tendsto (fun i => 16 * (t i : ℝ)) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hcoe.const_mul (16 : ℝ)
  have hsmall : ∀ᶠ i in l, (t i : ℝ) < (1 / 16 : ℝ) :=
    hcoe.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hbound : ∀ᶠ i in l,
      |(inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            (H i) 2 (by norm_num)
            (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i) : ℝ)
            (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i)).property)
          (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)) /
        (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i) : ℝ) +
        (1 / 4 : ℝ)| ≤ 16 * (t i : ℝ) := by
    filter_upwards [hpos, hsmall] with i hi hsmalli
    exact p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlopeError_le
      (H i) (t i) hi hsmalli.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscaled
    (Eventually.of_forall fun i => abs_nonneg _) hbound

/-- The actual normalized overlap tends to -1/4 even along arbitrary moving
finite volumes, under the explicit volume-dependent coupling substitution. -/
theorem p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlope_tendsto_neg_quarter
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ι → ℕ) (t : ι → ℝ≥0)
    (ht : Tendsto t l (𝓝 (0 : ℝ≥0)))
    (hpos : ∀ᶠ i in l, 0 < t i) :
    Tendsto
      (fun i =>
        (inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              (H i) 2 (by norm_num)
              (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i) : ℝ)
              (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i)).property)
            (p4Q2PZ37AMU_actualPhysicalGaussMode (H i) 1)) /
          (p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta (H i) (t i) : ℝ))
      l (𝓝 (-(1 / 4 : ℝ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs, sub_neg_eq_add] using
    p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlopeError_tendsto_zero l H t ht hpos

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOB_originalPhysicalBudgetRescaledBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlopeError_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlopeError_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOB_originalPhysicalTopFirst_rescaledSlope_tendsto_neg_quarter
