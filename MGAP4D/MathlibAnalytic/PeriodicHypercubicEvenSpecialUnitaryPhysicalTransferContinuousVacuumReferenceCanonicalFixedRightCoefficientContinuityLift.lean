import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightBarrierContinuation
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

/-!
# Lift coordinate response continuity to the exact canonical coefficient

The barrier-continuation theorem only needs continuity of the exact scalar
coefficient path.  Since that coefficient is a finite maximum of finite
weighted sums, all of its continuity is formal once the individual canonical
fixed-right response coordinates are continuous in the coupling.

This file makes that reduction explicit.

For each ordered target/source pair we define a total beta-path by filling
negative coupling with zero.  We similarly package each normalized weighted
column.  The exact coefficient path is then identified with a finite
`Finset.sup'` over source columns.  Standard continuity of finite sums and
finite suprema transports coordinate continuity all the way to `M_can`.

Thus after this theorem unit the only model-facing continuation input is:

  every canonical response coordinate beta |-> R_can(target,source; beta)
  is continuous on the selected nonnegative high-temperature interval.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance canonicalFixedRightCoefficientContinuityLiftSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalFixedRightCoefficientContinuityLiftSpatialLinkNonempty
    (H : ℕ) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) := by
  refine ⟨
    (⟨(0 : PeriodicHypercubicEvenVertex H), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨(1 : PeriodicHypercubicAxis), by decide⟩)⟩

/-- Total beta-path of one canonical fixed-right response coordinate. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
    (H N : ℕ)
    (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) : ℝ :=
  if hbeta : 0 ≤ beta then
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta target source
  else 0

/-- On nonnegative coupling the response path is the actual canonical profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath_eq
    (H N : ℕ)
    (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
        H N hN target source beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath,
    hbeta]

/-- Total beta-path of one source-normalized weighted canonical column. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) : ℝ :=
  if hbeta : 0 ≤ beta then
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
      H N hN beta hbeta s center source
  else 0

/-- A normalized column path is exactly the finite weighted sum of the
coordinate response paths divided by the fixed source weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath_eq_sum_div
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath
        H N hN s center source beta =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
            H N hN target source beta *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  classical
  by_cases hbeta : 0 ≤ beta
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn,
      hbeta]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath,
      hbeta]

/-- Coordinatewise continuity implies continuity of each normalized weighted
column, because the target set is finite and the denominator is a fixed
strictly positive spatial weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath_continuousOn_of_responseProfilePath
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (K : Set ℝ)
    (hResponse :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        ContinuousOn
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
            H N hN target source)
          K) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath
        H N hN s center source)
      K := by
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hWSource : W source ≠ 0 := by
    exact ne_of_gt
      (by
        simpa [W] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
            H s hsPos center source)
  have hTerms :
      ∀ target ∈ (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
        ContinuousOn
          (fun beta =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
                H N hN target source beta *
              W target)
          K := by
    intro target _hTarget
    exact (hResponse target).mul continuousOn_const
  have hSum :
      ContinuousOn
        (fun beta =>
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
                H N hN target source beta *
              W target)
        K := by
    exact continuousOn_finsetSum Finset.univ hTerms
  have hDiv :
      ContinuousOn
        (fun beta =>
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
                H N hN target source beta *
              W target) / W source)
        K := by
    exact hSum.div continuousOn_const (fun _ _ => hWSource)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath_eq_sum_div,
    W] using hDiv

/-- The exact coefficient path is the finite supremum of the normalized
source-column paths. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_eq_sup'
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center beta =
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).sup'
        Finset.univ_nonempty
        (fun source =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath
            H N hN s center source beta) := by
  classical
  by_cases hbeta : 0 ≤ beta
  · rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_eq
        H N hN s center beta hbeta]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnValues
    rw [Finset.max'_eq_sup']
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath,
      hbeta] using
      (Finset.sup'_image
        (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
        (f :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
            H N hN beta hbeta s center)
        (hs :=
          (Finset.univ.image
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
              H N hN beta hbeta s center)).nonempty)
        (g := id))
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath,
      hbeta]

/-- Continuity of all normalized source columns lifts through the finite maximum
to continuity of the exact canonical coefficient path. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_of_columns
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (K : Set ℝ)
    (hColumns :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        ContinuousOn
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath
            H N hN s center source)
          K) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center)
      K := by
  let S : Finset (PeriodicHypercubicEvenSpatialSliceLink H) := Finset.univ
  have hSup :
      ContinuousOn
        (fun beta =>
          S.sup' (by simpa [S] using
            (Finset.univ_nonempty :
              (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).Nonempty))
            (fun source =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath
                H N hN s center source beta))
        K := by
    apply ContinuousOn.finset_sup'_apply
    intro source hSource
    exact hColumns source
  simpa [
    S,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_eq_sup'] using
    hSup

/-- Pairwise canonical response continuity is sufficient for continuity of the
exact finite-volume coefficient path. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_of_responseProfilePath
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (K : Set ℝ)
    (hResponse :
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        ContinuousOn
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
            H N hN target source)
          K) :
    ContinuousOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath
        H N hN s center)
      K := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_of_columns
      H N hN s center K
  intro source
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnPath_continuousOn_of_responseProfilePath
      H N hN s hs center source K
      (fun target => hResponse target source)

/-- On the established high-temperature interval, coordinate response
continuity alone closes the no-jump step and forces the actual exact canonical
coefficient below one half. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_lt_halfBarrier_of_responseProfilePath_continuousOn
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (hResponse :
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        ContinuousOn
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfilePath
            H N hN target source)
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
  have hContinuous :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficientPath_continuousOn_of_responseProfilePath
      H N hN s hs center
      (Set.Icc 0
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s))
      hResponse
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_lt_halfBarrier_of_continuousOn
      H N hN s hs center hContinuous beta hBeta hBetaCutoff

end

end MathlibAnalytic
end MGAP4D
