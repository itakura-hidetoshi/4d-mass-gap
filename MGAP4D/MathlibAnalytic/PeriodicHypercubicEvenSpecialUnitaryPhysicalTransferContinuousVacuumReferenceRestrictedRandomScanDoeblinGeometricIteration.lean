import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanDoeblinGeometricBlockContraction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

local instance referenceRestrictedRandomScanDoeblinGeometricIterationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanDoeblinGeometricIterationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanDoeblinGeometricIterationSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanDoeblinGeometricIterationSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanDoeblinGeometricIterationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanDoeblinGeometricIterationSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The real-valued fixed-volume Doeblin residual factor is strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_toReal_lt_one
    (H : ℕ)
    (beta : ℝ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta).toReal < 1 := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_named_lt_one
      H beta
  simpa using
    (ENNReal.toReal_lt_toReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_ne_top
        H beta)
      ENNReal.one_ne_top).2 h

/-- Full-block expectation preserves strong measurability of real observables. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation_stronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
        H N hN beta hbeta B target source k g₂ f) := by
  have hIter :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_stronglyMeasurable
      H N hN beta hbeta B target source k g₂ f hf 1
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
  ] using hIter

/-- The geometric fixed-volume Doeblin factor tends to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_toReal_pow_tendsto_zero
    (H : ℕ)
    (beta : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
          H beta).toReal ^ n)
      atTop
      (𝓝 0) := by
  exact
    tendsto_pow_atTop_nhds_zero_of_lt_one
      ENNReal.toReal_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_toReal_lt_one
        H beta)

end

end MathlibAnalytic
end MGAP4D
