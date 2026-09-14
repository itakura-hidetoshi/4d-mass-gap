import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedCarrier
import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelMaximumColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A right-tag source column collapses to the same single matching-coordinate
C5 contraction coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_rightColumnSum_eq_coefficient
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        (Sum.inr source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta := by
  classical
  unfold finiteInfluenceKernelColumnSum
  rw [Fintype.sum_sum_type]
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence,
    Finset.sum_const_zero,
    add_zero]
  rw [Finset.sum_eq_single source]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]
  · intro fiber _hfiber hne
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      Ne.symm hne]
  · simp

/-- Every left-tag source column is exactly zero in this one-way carrier. This
is a carrier-scope statement: the carrier contains only proved right-source to
left-target influence and does not assert a reverse physical vanishing law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_leftColumnSum_eq_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        (Sum.inl source) = 0 := by
  classical
  unfold finiteInfluenceKernelColumnSum
  rw [Fintype.sum_sum_type]
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence]

/-- Every tagged source column is bounded by the same volume-independent C5
coefficient.  The left-source case is the carrier-scope zero column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_columnSum_le_coefficient
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta := by
  cases source with
  | inl source =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_leftColumnSum_eq_zero]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
          beta hbeta
  | inr source =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_rightColumnSum_eq_coefficient]

/-- Below the explicit C5 threshold every tagged source column is strictly
contractive, uniformly in the spatial volume. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_columnSum_lt_one_of_beta_lt
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (source :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        source < 1 := by
  exact lt_of_le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_columnSum_le_coefficient
      H beta hbeta source)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_lt_one_of_beta_lt
      beta hBetaLt)

/-- The tagged left/right spatial-link index is nonempty for every even-periodic
size parameter. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
    (H : ℕ) :
    0 <
      Fintype.card
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let vertex : PeriodicHypercubicEvenSpatialSliceVertex H :=
    ⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩
  let direction : PeriodicHypercubicEvenSpatialDirection :=
    ⟨1, by norm_num⟩
  exact Fintype.card_pos_iff.mpr ⟨Sum.inl (vertex, direction)⟩

/-- The generic reciprocal random-scan rate induced by the tagged column
coefficient is strictly below one in the same C5 small-coupling regime. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_reciprocalRandomScanRate_lt_one
    (H : ℕ)
    (beta : ℝ)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold) :
    finiteInfluenceKernelReciprocalRandomScanRate
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta) < 1 := by
  exact
    finiteInfluenceKernelReciprocalRandomScanRate_lt_one
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
        H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_lt_one_of_beta_lt
        beta hBetaLt)

/-- The tagged C5 column certificate feeds directly into the generic reciprocal
random-scan one-step response bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_randomScanUpdatedVariation_le_rate_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (source :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) :
    finiteInfluenceKernelRandomScanUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        variation source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) * bound := by
  exact
    finiteInfluenceKernelRandomScanUpdatedVariation_le_rate_mul
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
        H beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
        H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
        beta hbeta)
      (fun source =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_columnSum_le_coefficient
          H beta hbeta source)
      variation hVariationNonneg bound hBoundNonneg hVariationBound source

/-- RED probe: iteration of the same tagged one-way carrier should contract the
supremum profile by the reciprocal rate to the `n`th power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_randomScanVariationIterate_le_rate_pow_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (n : ℕ)
    (source :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) :
    finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        variation n source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^ n * bound := by
  rfl

end

end MathlibAnalytic
end MGAP4D
