import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstRowMomentSlopeV5_PZ37AOS
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOT — original finite-H Wilson Haar row right-slope error

Source-bound DIAGNOSTIC CANDIDATE only. The original SU(2) Wilson
one-slab Boltzmann kernel, normalized spatial-slice Haar, primary character,
fixed left boundary and original physical objects are unchanged.

The already formally certified AOS error is O(beta^2), with constant
(32 + 4*C_H) dependent on finite H. Positive beta permits division,
yielding a quantitative ratio estimate. No H-uniform limit, physical
spectral gap, or continuum Yang--Mills mass gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

/-- The actual original SU(2) Wilson first-Haar-row moment divided by
positive coupling differs from 1/8 by at most (32+4*C_H)*beta.
This is not a proof of a uniform-H right derivative or mass gap. -/
theorem p4Q2PZ37AOT_originalFirstRowHaarMoment_quotientError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta) (hsmall : 8 * beta ≤ 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |((∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) /
        beta) - (1 / 8 : ℝ)| ≤
      (32 + 4 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
        beta := by
  let I : ℝ :=
    ∫ B,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hBound : |I - beta / 8| ≤ (32 + 4 * C) * beta^2 :=
    p4Q2PZ37AOS_originalFirstRowHaarMoment_quadraticError_abs_le
      H beta hbeta.le hsmall A
  have hEq : I / beta - (1 / 8 : ℝ) = (I - beta / 8) / beta := by
    field_simp [ne_of_gt hbeta]
  change |I / beta - (1 / 8 : ℝ)| ≤ (32 + 4 * C) * beta
  rw [hEq, abs_div, abs_of_pos hbeta]
  apply (div_le_iff₀ hbeta).2
  calc
    |I - beta / 8| ≤ (32 + 4 * C) * beta^2 := hBound
    _ = ((32 + 4 * C) * beta) * beta := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOT_originalFirstRowHaarMoment_quotientError_le
