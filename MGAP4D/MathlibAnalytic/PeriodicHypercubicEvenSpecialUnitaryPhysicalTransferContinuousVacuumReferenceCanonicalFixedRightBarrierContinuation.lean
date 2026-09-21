import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHalfBarrier
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Canonical fixed-right half-barrier continuation

The previous theorem unit proves, on one explicit volume-independent
high-temperature interval, that the exact canonical weighted response
coefficient can never equal the numerical barrier 1/2.

To convert that pointwise barrier exclusion into the strict bound
`M_can < 1/2`, only a no-jump input is still needed.  This file isolates that
input exactly.

Because the canonical coefficient carries a proof parameter
`hbeta : 0 <= beta`, we first package it as a total real-valued path by
returning zero on negative coupling.  On nonnegative coupling this path is
definitionally the exact canonical coefficient, and at beta = 0 it is exactly
zero.

The main theorem is then just the intermediate value theorem:

* the path starts at 0, strictly below 1/2;
* throughout the selected high-temperature interval the exact coefficient is
  never equal to 1/2;
* therefore any continuous path cannot cross from below 1/2 to above it.

No continuity assertion for the Wilson canonical response is assumed to have
already been proved.  The theorem below takes that continuity as its sole
analytic input, so the remaining model-facing obligation is now explicit.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Total real-valued path associated with the exact canonical weighted
response coefficient.  Negative couplings are filled with zero only so that
ordinary real continuity statements can be formulated without a dependent
proof argument. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) : ℝ :=
  if hbeta : 0 ≤ beta then
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      H N hN beta hbeta s center
  else 0

/-- On nonnegative coupling, the total path is the exact canonical
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_eq
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath,
    hbeta]

/-- The total coefficient path starts at zero. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_zero
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_beta_zero
      H N hN s center]

/-- Continuous first-crossing exclusion on the selected high-temperature
interval.  This is the exact no-jump continuation statement needed after the
merged half-barrier exclusion theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_lt_halfBarrier_of_continuousOn
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (hContinuous :
      ContinuousOn
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
          H N hN s center)
        (Set.Icc 0
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
            s)))
    (beta : ℝ)
    (hBeta :
      beta ∈ Set.Icc 0
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center beta <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
      H N hN s center
  let barrier :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier
  let cutoff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
      s
  have hMZero : M 0 = 0 := by
    simp [M]
  have hBarrierPos : 0 < barrier := by
    norm_num [
      barrier,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]
  by_contra hNot
  have hBarrierLe : barrier ≤ M beta :=
    le_of_not_gt hNot
  have hInterval : barrier ∈ Set.Icc (M 0) (M beta) := by
    rw [hMZero]
    exact ⟨hBarrierPos.le, hBarrierLe⟩
  have hContinuousRestricted :
      ContinuousOn M (Set.Icc 0 beta) := by
    apply hContinuous.mono
    intro x hx
    exact ⟨hx.1, hx.2.trans hBeta.2⟩
  have hImage :=
    intermediate_value_Icc hBeta.1 hContinuousRestricted hInterval
  rcases hImage with ⟨crossing, hCrossingInterval, hCrossingEq⟩
  have hCrossingNeZero : crossing ≠ 0 := by
    intro hZero
    subst crossing
    rw [hMZero] at hCrossingEq
    linarith
  have hCrossingPos : 0 < crossing :=
    lt_of_le_of_ne hCrossingInterval.1 (Ne.symm hCrossingNeZero)
  have hCrossingCutoff : crossing ≤ cutoff := by
    exact hCrossingInterval.2.trans hBeta.2
  have hActualNe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_ne_halfBarrier_of_le_cutoff
      H N hN s hs crossing hCrossingPos hCrossingCutoff center
  have hPathEq :
      M crossing =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN crossing hCrossingPos.le s center := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_eq
        H N hN s center crossing hCrossingPos.le
  have hActualEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN crossing hCrossingPos.le s center =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
    exact hPathEq.symm.trans hCrossingEq
  exact hActualNe hActualEq

/-- Endpoint form: continuity of the exact coefficient path on the fixed
volume-independent high-temperature interval forces the actual canonical
coefficient strictly below one half at every positive coupling in that
interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_lt_halfBarrier_of_continuousOn
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (hContinuous :
      ContinuousOn
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
          H N hN s center)
        (Set.Icc 0
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
            s)))
    (beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hBeta.le s center <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  have hPath :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_lt_halfBarrier_of_continuousOn
      H N hN s hs center hContinuous beta
      ⟨hBeta.le, hBetaCutoff⟩
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath,
    hBeta.le] using hPath

end

end MathlibAnalytic
end MGAP4D
