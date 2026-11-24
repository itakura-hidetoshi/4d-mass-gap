import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstRowRightSlopeLimitV5_PZ37AOU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOV — original Wilson first Haar row, moving-volume slope

Diagnostic candidate, not independently certified. AOP controls the true
unnormalized row moment by the actual row-mass deficit. Division by positive
beta retains this sharper condition instead of replacing it by a global
action budget. Both moving-volume limits are scalar statements, using the
unchanged original Wilson kernel and Haar measure. No fixed positive beta,
infinite-volume state, physical spectral gap, or continuum mass gap follows.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "C" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget

/-- AOP's actual row-mass-deficit bound after division by positive beta. -/
theorem p4Q2PZ37AOV_originalFirstRowHaarMoment_quotientError_le_deficit
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hsmall : 8 * beta ≤ 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |((∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) /
        beta) - (1 / 8 : ℝ)| ≤
      32 * beta + 4 * (1 - (∫ B,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))) := by
  let I : ℝ := ∫ B,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  let Z : ℝ := ∫ B,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  have hResponse : |(-2 : ℝ) * I + beta / 4| ≤
      64 * beta^2 + 8 * beta * (1 - Z) :=
    p4Q2PZ37AOP_originalRowResponse_abs_error_le_rowMassDeficit
      H beta hbeta.le hsmall A
  have hScale : (-2 : ℝ) * (I - beta / 8) = (-2 : ℝ) * I + beta / 4 := by ring
  rw [← hScale, abs_mul] at hResponse
  norm_num at hResponse
  have hEq : I / beta - (1 / 8 : ℝ) = (I - beta / 8) / beta := by
    field_simp [ne_of_gt hbeta]
  change |I / beta - (1 / 8 : ℝ)| ≤ 32 * beta + 4 * (1 - Z)
  rw [hEq, abs_div, abs_of_pos hbeta]
  apply (div_le_iff₀ hbeta).2
  calc
    |I - beta / 8| ≤ (64 * beta^2 + 8 * beta * (1 - Z)) / 2 := by
      linarith only [hResponse]
    _ = (32 * beta + 4 * (1 - Z)) * beta := by ring

/-- The original Haar row slope with arbitrarily moving volume and boundary
converges to 1/8 when beta and the actual row-mass deficit both vanish. -/
theorem p4Q2PZ37AOV_originalFirstRowHaarMoment_movingDeficitSlope_tendsto_eighth
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ι → ℕ)
    (A : (i : ι) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (H i) 2)
    (beta : ι → ℝ)
    (hzero : Tendsto beta l (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ i in l, 0 < beta i)
    (hdeficit : Tendsto (fun i => 1 - (∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        (H i) 2 (beta i) (A i) B
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (H i) 2)))
      l (𝓝 (0 : ℝ))) :
    Tendsto (fun i => (∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        (H i) 2 (beta i) (A i) B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy (H i) 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (H i) 2)) / beta i)
      l (𝓝 (1 / 8 : ℝ)) := by
  let I : ι → ℝ := fun i => ∫ B,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      (H i) 2 (beta i) (A i) B *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy (H i) 2 B)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (H i) 2)
  let d : ι → ℝ := fun i => 1 - (∫ B,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      (H i) 2 (beta i) (A i) B
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (H i) 2))
  change Tendsto (fun i => I i / beta i) l (𝓝 (1 / 8 : ℝ))
  have hEight : Tendsto (fun i => (8 : ℝ) * beta i) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (8 : ℝ)
  have hsmall : ∀ᶠ i in l, 8 * beta i < (1 : ℝ) :=
    hEight.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hd : Tendsto d l (𝓝 (0 : ℝ)) := hdeficit
  have h32 : Tendsto (fun i => (32 : ℝ) * beta i) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (32 : ℝ)
  have h4 : Tendsto (fun i => (4 : ℝ) * d i) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hd.const_mul (4 : ℝ)
  have hUpper : Tendsto (fun i => 32 * beta i + 4 * d i) l (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using h32.add h4
  have hBound : ∀ᶠ i in l, |I i / beta i - (1 / 8 : ℝ)| ≤ 32 * beta i + 4 * d i := by
    filter_upwards [hpos, hsmall] with i hi hs
    exact p4Q2PZ37AOV_originalFirstRowHaarMoment_quotientError_le_deficit
      (H i) (beta i) hi hs.le (A i)
  have hError : Tendsto (fun i => |I i / beta i - (1 / 8 : ℝ)|) l (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
      (Eventually.of_forall fun i => abs_nonneg _) hBound
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hError

/-- A sufficient diagonal condition from the certified original action-budget
error AOT. It allows arbitrary dependent boundaries and moving volumes,
but requires the physical coupling to vanish and its budget product to vanish. -/
theorem p4Q2PZ37AOV_originalFirstRowHaarMoment_movingBudgetSlope_tendsto_eighth
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ι → ℕ)
    (A : (i : ι) → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (H i) 2)
    (beta : ι → ℝ)
    (hzero : Tendsto beta l (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ i in l, 0 < beta i)
    (hbudget : Tendsto (fun i => beta i * C (H i)) l (𝓝 (0 : ℝ))) :
    Tendsto (fun i => (∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        (H i) 2 (beta i) (A i) B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy (H i) 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (H i) 2)) / beta i)
      l (𝓝 (1 / 8 : ℝ)) := by
  let I : ι → ℝ := fun i => ∫ B,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      (H i) 2 (beta i) (A i) B *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy (H i) 2 B)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (H i) 2)
  change Tendsto (fun i => I i / beta i) l (𝓝 (1 / 8 : ℝ))
  have hEight : Tendsto (fun i => (8 : ℝ) * beta i) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (8 : ℝ)
  have hsmall : ∀ᶠ i in l, 8 * beta i < (1 : ℝ) :=
    hEight.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have h32 : Tendsto (fun i => (32 : ℝ) * beta i) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (32 : ℝ)
  have h4 : Tendsto (fun i => (4 : ℝ) * (beta i * C (H i))) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hbudget.const_mul (4 : ℝ)
  have hUpper : Tendsto (fun i => 32 * beta i + 4 * (beta i * C (H i)))
      l (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using h32.add h4
  have hBound : ∀ᶠ i in l, |I i / beta i - (1 / 8 : ℝ)| ≤
      32 * beta i + 4 * (beta i * C (H i)) := by
    filter_upwards [hpos, hsmall] with i hi hs
    calc
      _ ≤ (32 + 4 * C (H i)) * beta i :=
        p4Q2PZ37AOT_originalFirstRowHaarMoment_quotientError_le
          (H i) (beta i) hi hs.le (A i)
      _ = _ := by ring
  have hError : Tendsto (fun i => |I i / beta i - (1 / 8 : ℝ)|) l (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
      (Eventually.of_forall fun i => abs_nonneg _) hBound
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hError

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOV_originalFirstRowHaarMoment_quotientError_le_deficit
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOV_originalFirstRowHaarMoment_movingDeficitSlope_tendsto_eighth
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOV_originalFirstRowHaarMoment_movingBudgetSlope_tendsto_eighth
