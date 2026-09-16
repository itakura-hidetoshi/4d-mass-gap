import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOffTargetHeatBathRawVacuumDoobBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRemoteSlabCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceRemoteVacuumOnlyDoobSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRemoteVacuumOnlyDoobSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRemoteVacuumOnlyDoobSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRemoteVacuumOnlyDoobSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRemoteVacuumOnlyDoobSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A remote update of the base spatial configuration leaves the raw one-slab
link weight unchanged whenever the updated link is distinct from the resampled
link and shares no spatial Wilson plaquette with it. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight_update_remote_eq
    (H N : ℕ)
    (beta : ℝ)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (u g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hDistinct : backgroundFiber ≠ fiber)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H fiber backgroundFiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight
        H N beta C (Function.update A backgroundFiber u) fiber g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight
        H N beta C A fiber g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight
  apply congrArg ENNReal.ofReal
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
      H N beta C A fiber backgroundFiber u g hDistinct hNoShare

/-- Consequently the normalized raw one-slab link law itself is exactly
unchanged by such a remote base update. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure_update_remote_eq
    (H N : ℕ)
    (beta : ℝ)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (u : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hDistinct : backgroundFiber ≠ fiber)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H fiber backgroundFiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
        H N beta C (Function.update A backgroundFiber u) fiber =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
        H N beta C A fiber := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
  apply congrArg
    (fun w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ =>
      doobWeightedMeasure
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) w)
  funext g
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight_update_remote_eq
      H N beta C A fiber backgroundFiber u g hDistinct hNoShare

/-- For an off-target resampled fiber and a spatially remote background update,
the literal C5 reference-fiber law has a common raw one-slab base measure.
All dependence on the remote background value is isolated in the canonical
continuous-vacuum Doob weight.

This is an exact normalized-measure decomposition.  It does not assert decay of
the vacuum response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_update_remote_eq_commonRaw_vacuumDoob
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberTarget : fiber ≠ target)
    (hBackgroundFiberDistinct : backgroundFiber ≠ fiber)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H fiber backgroundFiber)
    (k g₂ u : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber u) =
      doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta (Function.update B source k) A fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta (Function.update A backgroundFiber u) fiber) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_raw_vacuum_doob_of_ne_target
      H N hN beta hbeta B target source fiber hFiberTarget k g₂
      (Function.update A backgroundFiber u),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure_update_remote_eq
      H N beta (Function.update B source k) A fiber backgroundFiber u
      hBackgroundFiberDistinct hNoShare]

/-- Two remote background values therefore produce two Doob reweightings of
one and the same raw one-slab probability law.  This is the exact measure-level
normal form needed before any non-circular estimate of the vacuum response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_pair_eq_commonRaw_vacuumDoob
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberTarget : fiber ≠ target)
    (hBackgroundFiberDistinct : backgroundFiber ≠ fiber)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H fiber backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber u) =
      doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta (Function.update B source k) A fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta (Function.update A backgroundFiber u) fiber) ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂
        (Function.update A backgroundFiber v) =
      doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta (Function.update B source k) A fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta (Function.update A backgroundFiber v) fiber) := by
  constructor
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_update_remote_eq_commonRaw_vacuumDoob
        H N hN beta hbeta B target source fiber backgroundFiber
        hFiberTarget hBackgroundFiberDistinct hNoShare k g₂ u A
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_update_remote_eq_commonRaw_vacuumDoob
        H N hN beta hbeta B target source fiber backgroundFiber
        hFiberTarget hBackgroundFiberDistinct hNoShare k g₂ v A

end

end MathlibAnalytic
end MGAP4D
