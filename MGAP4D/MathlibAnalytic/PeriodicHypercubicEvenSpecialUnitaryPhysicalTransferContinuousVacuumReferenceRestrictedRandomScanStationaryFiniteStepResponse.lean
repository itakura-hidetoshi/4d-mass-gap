import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanStationaryResponseResidual
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceRestrictedRandomScanStationaryFiniteStepResponseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Finite-step stationary response decomposition for the actual restricted
continuous-C5 random scan.  The first term is the accumulated source forcing
already carried by the tagged physical transport iterate.  The second term is
the terminal response of the common `k`-boundary smoothed observable.

This is the concrete continuous-state `R ≤ D + Q R` finite-step interface. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_response_abs_le_taggedTransport_add_terminal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (hFh : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source h g₂))
    (hFk : Integrable F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂))
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e)
    (n : ℕ) :
    |(∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source h g₂) -
      (∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta variation n (Sum.inr source) +
        |(∫ A,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k F n A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source h g₂) -
          (∫ A,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k F n A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂)| := by
  rfl

end

end MathlibAnalytic
end MGAP4D
