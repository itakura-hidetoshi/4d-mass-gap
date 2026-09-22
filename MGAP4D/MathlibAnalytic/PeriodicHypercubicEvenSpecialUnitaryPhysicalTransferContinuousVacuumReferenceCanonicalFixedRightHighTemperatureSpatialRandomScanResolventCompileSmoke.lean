import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureSpatialRandomScanResolvent

namespace MGAP4D.MathlibAnalytic

noncomputable section

local instance canonicalHighTemperatureSpatialRandomScanResolventCompileSmokeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

#check finiteInfluenceColumnIterateKernel_eq_finiteInfluenceIterateKernel
#check finiteInfluenceKernelRandomScanUpdatedVariation_card_mul_eq
#check finiteInfluenceKernelRandomScanVariationPartialSum_resolvent_identity
#check finiteInfluenceKernelRandomScanFiniteResolventProfile
#check finiteInfluenceKernelRandomScanFiniteResolventProfile_nonneg
#check finiteInfluenceKernelRandomScanFiniteResolventProfile_subinvariant
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_eq_kernel
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_subinvariant
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_weightedResolvent
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_spatialResolvent_of_distance

/-- The closed beta = 0 endpoint is retained at arbitrary growing scale. -/
example
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (hcut :
      (0 : ℝ) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (D : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        variation target ≠ 0 →
          D ≤
            periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
    (M : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN 0 le_rfl variation M source ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s 0)⁻¹ *
        (s ^ D)⁻¹ *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          variation target) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_spatialResolvent_of_distance
      H N hN s hs 0 le_rfl hcut variation hVariationNonneg
      D source hDistance M

/-- At s = 1 the same theorem is retained as a uniform resolvent statement,
without claiming spatial exponential decay. -/
example
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (D : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        variation target ≠ 0 →
          D ≤
            periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
    (M : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M source ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          1 beta)⁻¹ *
        ((1 : ℝ) ^ D)⁻¹ *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          variation target) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_spatialResolvent_of_distance
      H N hN 1 (by norm_num) beta hbeta hcut
      variation hVariationNonneg D source hDistance M

end

end MGAP4D.MathlibAnalytic
