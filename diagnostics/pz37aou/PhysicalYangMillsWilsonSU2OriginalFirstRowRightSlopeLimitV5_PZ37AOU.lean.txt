import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFirstRowSlopeV5_PZ37AOT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOU — original fixed-volume Wilson/Haar first-row right-slope limit

DIAGNOSTIC Lean candidate, not independently certified.

For a FIXED finite H and FIXED left spatial SU(2) boundary A, the genuine
original one-slab Wilson/Haar first-character moment divided by beta has
limit 1/8 along every filter of eventually positive beta tending to zero.
The proof combines the already certified AOT quotient error with a
filtered order-theoretic squeeze. The H-dependent original action budget
is held fixed, not replaced by an H-uniform constant.

No claim is made about a moving-volume positive coupling, physical
Hamiltonian spectral gap, or continuum 4D Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

/-- Along any eventually positive coupling sequence or filter tending
to zero, the genuine original fixed-H Wilson first-Haar row quotient
converges to its explicit coefficient 1/8. Not an H-uniform limit. -/
theorem p4Q2PZ37AOU_originalFirstRowHaarMoment_quotient_tendsto_eighth
    {ι : Type*} (l : Filter ι) [NeBot l]
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (beta : ι → ℝ)
    (hzero : Tendsto beta l (𝓝 (0 : ℝ)))
    (hpos : ∀ᶠ i in l, 0 < beta i) :
    Tendsto
      (fun i =>
        (∫ B,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H 2 (beta i) A B *
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) /
            beta i)
      l (𝓝 (1 / 8 : ℝ)) := by
  let C : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hEight : Tendsto
      (fun i => (8 : ℝ) * beta i) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (8 : ℝ)
  have hsmall : ∀ᶠ i in l, 8 * beta i < (1 : ℝ) :=
    hEight.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hUpper : Tendsto
      (fun i => (32 + 4 * C) * beta i) l (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hzero.const_mul (32 + 4 * C)
  have hBound : ∀ᶠ i in l,
      |((∫ B,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 (beta i) A B *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) /
          beta i) - (1 / 8 : ℝ)| ≤
        (32 + 4 * C) * beta i := by
    filter_upwards [hpos, hsmall] with i hi hs
    exact p4Q2PZ37AOT_originalFirstRowHaarMoment_quotientError_le
      H (beta i) hi hs.le A
  have hError : Tendsto
      (fun i =>
        |((∫ B,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H 2 (beta i) A B *
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) /
            beta i) - (1 / 8 : ℝ)|)
      l (𝓝 (0 : ℝ)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpper
      (Eventually.of_forall fun i => abs_nonneg _) hBound
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using hError

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOU_originalFirstRowHaarMoment_quotient_tendsto_eighth
