import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationarySourceAverage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedReciprocalSweepExponentialSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One full tagged random-scan sweep converts the finite-volume reciprocal
rate into a volume-independent exponential envelope.  The exponent is the
C5 gap `1 - q(beta)` per sweep; no volume-uniform one-coordinate rate is
asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_reciprocalRandomScanRate_pow_card_mul_le_expSweep
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (sweeps : ℕ) :
    finiteInfluenceKernelReciprocalRandomScanRate
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) * sweeps) ≤
      Real.exp
        (-(1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
              beta) * (sweeps : ℝ)) := by
  let q : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
      beta
  let N : ℕ :=
    Fintype.card
      (Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H))
  let rate : ℝ :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) q
  let x : ℝ := (N : ℝ)⁻¹ * (1 - q)
  change rate ^ (N * sweeps) ≤
    Real.exp (-(1 - q) * (sweeps : ℝ))
  have hCard : 0 < N := by
    dsimp [N]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
        H
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
        beta hbeta
  have hqLtOne : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_lt_one_of_beta_lt
        beta hBetaLt
  have hGapNonneg : 0 ≤ 1 - q :=
    (sub_pos.mpr hqLtOne).le
  have hxNonneg : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hGapNonneg
  have hRateNonneg : 0 ≤ rate := by
    dsimp [rate]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hCard q hqNonneg
  have hComplement : 1 - rate = x := by
    dsimp [rate, x, N]
    exact
      one_sub_finiteInfluenceKernelReciprocalRandomScanRate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
          H)
        q
  have hRateEq : rate = 1 - x := by
    linarith
  have hStep : rate ≤ Real.exp (-x) := by
    rw [hRateEq]
    have hExp := Real.add_one_le_exp (-x)
    nlinarith
  have hPow :
      rate ^ (N * sweeps) ≤
        (Real.exp (-x)) ^ (N * sweeps) :=
    pow_le_pow_left₀ hRateNonneg hStep (N * sweeps)
  have hCardNe : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCard
  calc
    rate ^ (N * sweeps) ≤
        (Real.exp (-x)) ^ (N * sweeps) := hPow
    _ = Real.exp (((N * sweeps : ℕ) : ℝ) * (-x)) := by
      exact (Real.exp_nat_mul (-x) (N * sweeps)).symm
    _ = Real.exp (-(1 - q) * (sweeps : ℝ)) := by
      congr 1
      dsimp [x]
      rw [Nat.cast_mul]
      field_simp [hCardNe]
      <;> ring

end

end MathlibAnalytic
end MGAP4D
