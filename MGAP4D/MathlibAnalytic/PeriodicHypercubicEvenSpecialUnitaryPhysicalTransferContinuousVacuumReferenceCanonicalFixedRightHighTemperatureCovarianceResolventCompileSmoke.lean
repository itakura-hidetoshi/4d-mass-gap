import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureCovarianceResolvent

namespace MGAP4D.MathlibAnalytic

noncomputable section

local instance canonicalHighTemperatureCovarianceResolventCompileSmokeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

example
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (M : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M e := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_nonneg
      H N hN beta hbeta variation hVariationNonneg M e

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
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (M : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M e ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          1 beta)⁻¹ *
        bound := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_resolvent
      H N hN beta hbeta hcut variation hVariationNonneg
      bound hBoundNonneg hVariationBound M e

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_le_rate_pow_mul

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_nonneg

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScan_average_dot_variationIterates_eq_dot_finiteResolventProfile

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_resolvent

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureResolvent

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureUniform

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSection_realIntegralCovariance_abs_le_canonicalHighTemperatureResolvent

end

end MGAP4D.MathlibAnalytic
