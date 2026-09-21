import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHalfBarrier
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Canonical fixed-right continuous first exit

The preceding theorem unit gives a volume-independent interval on which the
actual exact canonical weighted response coefficient can never equal the
numerical barrier `1/2`.

This file isolates the only topological input needed to turn that equality
exclusion into a strict bound.  For fixed finite volume, rank, exponential
scale, and center, extend the actual canonical coefficient to a total real
parameter family by setting it to zero at negative coupling.  On the
nonnegative half-line this extension is exactly `M_can`, and at zero it is
exactly zero.

If this total family is continuous on `[0,beta]`, then it cannot move from
zero to or above the half barrier without attaining the barrier.  The merged
half-barrier exclusion theorem rules that attainment out at every positive
parameter below the common cutoff.  Therefore the endpoint actual coefficient
is strictly below `1/2`.

No continuity theorem is asserted here.  The purpose is to isolate the
remaining model-facing analytic obligation exactly as continuity of this
finite-volume coefficient family.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance canonicalFixedRightContinuousFirstExitSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalFixedRightContinuousFirstExitSpatialLinkNonempty
    (H : ℕ) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) := by
  refine ⟨
    (⟨(0 : PeriodicHypercubicEvenVertex H), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨(1 : PeriodicHypercubicAxis), by decide⟩)⟩

/-- Total real-parameter extension of the exact canonical weighted response
coefficient.  Negative couplings are assigned the harmless value zero; all
statements below use only the interval beginning at zero. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) : ℝ :=
  if hbeta : 0 ≤ beta then
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      H N hN beta hbeta s center
  else 0

/-- On nonnegative coupling the total extension is definitionally the actual
canonical coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily_eq_of_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily
        H N hN s center beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily
  simp [hbeta]

/-- The total coefficient extension starts exactly at zero. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily_zero
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily
        H N hN s center 0 = 0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily_eq_of_nonneg
      H N hN s center 0 (by norm_num)]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_beta_zero
      H N hN s center

/-- Continuous first-exit closure.  If the actual finite-volume canonical
coefficient family is continuous on the interval from zero to a positive
coupling below the common half-barrier cutoff, then the endpoint coefficient
lies strictly below one half. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_lt_halfBarrier_of_continuousOn
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (hContinuous :
      ContinuousOn
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily
          H N hN s center)
        (Set.Icc 0 beta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hBeta.le s center <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily
      H N hN s center
  have hMZero : M 0 = 0 := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily_zero
        H N hN s center
  have hEndpointEq :
      M beta =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN beta hBeta.le s center := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily_eq_of_nonneg
        H N hN s center beta hBeta.le
  by_contra hNot
  have hBarrierLeEndpoint :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier ≤
        M beta := by
    rw [hEndpointEq]
    exact le_of_not_gt hNot
  have hZeroLtBarrier :
      M 0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
    rw [hMZero]
    norm_num [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]
  have hBarrierInterval :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier ∈
        Set.Icc (M 0) (M beta) :=
    ⟨le_of_lt hZeroLtBarrier, hBarrierLeEndpoint⟩
  have hImage :=
    intermediate_value_Icc (le_of_lt hBeta)
      (by simpa [M] using hContinuous)
      hBarrierInterval
  rcases hImage with ⟨crossing, hCrossingInterval, hCrossingEq⟩
  have hCrossingNeZero : crossing ≠ 0 := by
    intro hZero
    subst crossing
    rw [hMZero] at hCrossingEq
    norm_num [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier] at
      hCrossingEq
  have hCrossingPos : 0 < crossing :=
    lt_of_le_of_ne hCrossingInterval.1 (Ne.symm hCrossingNeZero)
  have hCrossingCutoff :
      crossing ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hCrossingInterval.2.trans hBetaCutoff
  have hActualNe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_ne_halfBarrier_of_le_cutoff
      H N hN s hs crossing hCrossingPos hCrossingCutoff center
  have hFamilyEq :
      M crossing =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN crossing hCrossingPos.le s center := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientFamily_eq_of_nonneg
        H N hN s center crossing hCrossingPos.le
  apply hActualNe
  rw [← hFamilyEq]
  exact hCrossingEq

end

end MathlibAnalytic
end MGAP4D
