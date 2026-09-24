import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageTargetRMSMajorant
import Mathlib.Tactic

/-!
# Source-update decomposition of physical target-fiber centered means

The full physical one-link propagation has two distinct pieces. When an
off-target source value changes,

1. the concrete observable section itself changes because the retained
   off-target background changes;
2. even for one fixed concrete section, the target conditional law changes.

PR #4715 controls the second term by the actual physical envelope coefficient
times the target profile. This file isolates the exact additive decomposition,
leaving the first/direct term as the next RMS residual obligation. This is the
physical analogue of the background-change decomposition in the older hybrid
trajectory spine.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set

noncomputable section

local instance sourceUpdateMeanDecompositionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceUpdateMeanDecompositionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceUpdateMeanDecompositionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceUpdateMeanDecompositionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceUpdateMeanDecompositionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Retained off-target configuration after replacing one off-target source
link. -/
def periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
    {H : ℕ}
    {Gauge : Type*}
    [DecidableEq (PeriodicHypercubicEvenSpatialSliceLink H)]
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge)
    (value : Gauge) :
    PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Gauge :=
  Function.update retained ⟨source, hne.symm⟩ value

/-- Centered target-fiber mean of one concrete joint section under a physical
source-updated target law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) : ℝ :=
  ∫ g,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retained g - center
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update A source sourceValue)

/-- One physical source update splits into a direct observable-background
change plus the target-law response controlled by the actual full envelope.

The response hypothesis is quantified over every retained target background;
this is exactly what the context-uniform stage theorem is designed to supply. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdatedCenteredMean_difference_le_direct_add_envelope_mul_targetProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hResponse :
      ∀ retained' :
          PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionTargetResponseBoundedBy
          H N hN beta hbeta target F left B A retained'
          distinguishedSource k g₂ center profile)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained u)
          distinguishedSource k g₂ u center -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained v)
          distinguishedSource k g₂ v center| ≤
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained u)
          distinguishedSource k g₂ u center -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B A
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne retained v)
          distinguishedSource k g₂ u center| +
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile target := by
  let retainedV :=
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
      target source hne retained v
  let a :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
      H N hN beta hbeta target source F left B A
      (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne retained u)
      distinguishedSource k g₂ u center
  let b :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
      H N hN beta hbeta target source F left B A
      retainedV distinguishedSource k g₂ u center
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
      H N hN beta hbeta target source F left B A
      retainedV distinguishedSource k g₂ v center
  have hLaw :
      |b - c| ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile target := by
    have h :=
      hResponse retainedV source hne u v
    simpa [
      b, c, retainedV,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean] using h
  calc
    |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
    _ ≤
        |a - b| +
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source * profile target :=
      add_le_add_left hLaw _
    _ = _ := by
      rfl

end

end MGAP4D.MathlibAnalytic
