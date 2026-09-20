import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioFullResponseResolvent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

local instance fixedRightAsymptoticResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Sending the finite-step eligible-left geometric remainder to zero removes
all dependence on the scan depth from the remote fixed-right worst-case
cross-ratio majorant.

This is still a fixed-volume statement because the strict eligible-row
criterion uses the current coarse all-to-all left-left tagged coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_explicitEligibleRow_asymptotic_resolvent_of_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta B target source ≤
      Real.exp (16 * beta) *
        ((2 *
          (((Real.exp (8 * beta)) ^ 2 - 1) /
            ((Real.exp (8 * beta)) ^ 2 + 1))) *
          (Real.exp (16 * beta) *
            (1 -
              (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                  beta))⁻¹)) := by
  let rowCoefficient : ℝ :=
    (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta)
  let rate : ℝ :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H) rowCoefficient
  let diagonalCoefficient : ℝ :=
    2 *
      (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1))
  let asymptotic : ℝ :=
    Real.exp (16 * beta) *
      (diagonalCoefficient *
        (Real.exp (16 * beta) * (1 - rowCoefficient)⁻¹))
  have hRowNonneg : 0 ≤ rowCoefficient := by
    dsimp [rowCoefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedEligiblePullback_rowCoefficient_nonneg
        H beta hbeta
  have hRateNonneg : 0 ≤ rate := by
    dsimp [rate]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hCard rowCoefficient hRowNonneg
  have hRateLtOne : rate < 1 := by
    dsimp [rate]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_lt_one
        hCard rowCoefficient hEligibleRowLtOne
  have hPow :
      Tendsto (fun n : ℕ => rate ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hRateNonneg hRateLtOne
  have hTerminal :
      Tendsto
        (fun n : ℕ =>
          2 * (rate ^ n * Real.exp (16 * beta)))
        atTop (𝓝 0) := by
    have hScaled :
        Tendsto
          (fun n : ℕ => rate ^ n * Real.exp (16 * beta))
          atTop (𝓝 0) := by
      simpa using hPow.mul_const (Real.exp (16 * beta))
    simpa using hScaled.const_mul 2
  have hRhs :
      Tendsto
        (fun n : ℕ =>
          Real.exp (16 * beta) *
            (diagonalCoefficient *
                (Real.exp (16 * beta) * (1 - rowCoefficient)⁻¹) +
              2 * (rate ^ n * Real.exp (16 * beta))))
        atTop (𝓝 asymptotic) := by
    have hInside :
        Tendsto
          (fun n : ℕ =>
            diagonalCoefficient *
                (Real.exp (16 * beta) * (1 - rowCoefficient)⁻¹) +
              2 * (rate ^ n * Real.exp (16 * beta)))
          atTop
          (𝓝
            (diagonalCoefficient *
              (Real.exp (16 * beta) * (1 - rowCoefficient)⁻¹))) := by
      simpa using tendsto_const_nhds.add hTerminal
    simpa [asymptotic] using
      hInside.const_mul (Real.exp (16 * beta))
  have hFinite :
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
            H N hN beta hbeta B target source ≤
          Real.exp (16 * beta) *
            (diagonalCoefficient *
                (Real.exp (16 * beta) * (1 - rowCoefficient)⁻¹) +
              2 * (rate ^ n * Real.exp (16 * beta))) := by
    intro n
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_explicitEligibleRow_resolvent_of_remote
        H N hN beta hbeta hCard hEligibleRowLtOne B hne hNoShare n
    simpa [rowCoefficient, rate, diagonalCoefficient] using h
  have hLimit :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
          H N hN beta hbeta B target source ≤
        asymptotic := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hRhs
    exact Filter.Eventually.of_forall hFinite
  simpa [asymptotic, rowCoefficient, diagonalCoefficient] using hLimit

end

end MathlibAnalytic
end MGAP4D
