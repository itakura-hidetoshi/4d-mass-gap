import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointKernelSectionWeightedFubini
import Mathlib.Tactic

/-!
# Genuine joint and vacuum measure presentations by continuous kernel sections

PRs #4740--#4743 construct the measurable fixed-right kernel-section family,
orient the continuous joint density, and prove the exact weighted Fubini
identity with outer density `Omega_cont(C)^2`.

This file now identifies those continuous density presentations with the
historical physical measures already used by the theorem spine:

* the continuous vacuum-square density gives exactly the existing vacuum law;
* the fixed-left continuous joint density gives exactly the existing genuine
  ground-state joint law.

Only almost-everywhere representative replacement under `withDensity` is
used.  No new analytic estimate, source/target exchange, or pointwise
section-to-global norm comparison is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointKernelSectionMeasurePresentationTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointKernelSectionMeasurePresentationCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointKernelSectionMeasurePresentationSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointKernelSectionMeasurePresentationMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointKernelSectionMeasurePresentationBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointKernelSectionMeasurePresentationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Continuous presentation of the vacuum boundary law using the pointwise
canonical physical vacuum representative. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSquareMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
    (fun C =>
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C) ^ 2))

/-- Replacing the historical L2 vacuum representative by the canonical
continuous representative does not change the vacuum boundary measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_eq_continuousVacuumSquareMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSquareMeasure
        H N hN beta hbeta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSquareMeasure
  apply withDensity_congr_ae
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H N hN beta hbeta] with C hC
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
  rw [← hC]

/-- Continuous fixed-left density presentation of the genuine two-boundary
ground-state joint law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftContinuousMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).withDensity
    (fun z =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftKernelSectionFactor
          H N hN beta hbeta z))

/-- The continuous fixed-left kernel-section density gives exactly the existing
genuine ground-state joint measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_fixedLeftContinuousMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftContinuousMeasure
        H N hN beta hbeta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointFixedLeftContinuousMeasure
  apply withDensity_congr_ae
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedENNRealWeight_ae_eq_fixedLeftKernelSectionFactor
      H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
