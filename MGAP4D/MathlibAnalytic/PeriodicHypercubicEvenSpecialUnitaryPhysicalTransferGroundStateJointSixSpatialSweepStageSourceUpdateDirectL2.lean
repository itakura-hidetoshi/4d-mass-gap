import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateDirectRMS
import MGAP4D.MathlibAnalytic.RealIntegralPointwiseRMSResponseL2
import Mathlib.Tactic

/-!
# Pair-law L2 lift of the direct physical source-update response

PR #4720 proves the pointwise direct source-update estimate

  |Delta_direct(u,v)| <= sqrt(E_direct(u,v)).

PR #4718 gives the generic passage from a pointwise RMS bound to an integrated
L2 response bound.  This file combines them for an arbitrary source-value pair
measure.  No identification of that pair law with the eventual physical
hybrid/source law is assumed here.

The resulting coefficient is exactly one.  Thus the remaining physical task
is only to identify or bound the averaged direct energy by the genuine source
one-link residual energy.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance sourceUpdateDirectL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceUpdateDirectL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceUpdateDirectL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceUpdateDirectL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceUpdateDirectL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourceUpdateDirectL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The direct part of one source-update centered-mean change, with the target
law frozen at the first source value. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
      H N hN beta hbeta target source F left B A
      (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne retained u)
      distinguishedSource k g₂ u center -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
      H N hN beta hbeta target source F left B A
      (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne retained v)
      distinguishedSource k g₂ u center

/-- Integrating the #4720 pointwise direct RMS estimate against any source-value
pair law gives an L2 direct-response bound with coefficient one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdateDirectMeanDifference_pairL2_le_directEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) (center : ℝ)
    (pairLaw : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hDeltaSq : Integrable (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
        H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2 center ^ 2) pairLaw)
    (hEnergy : Integrable (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
        H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2) pairLaw) :
    Real.sqrt (∫ z,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
          H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2 center ^ 2
        ∂pairLaw) ≤
      Real.sqrt (∫ z,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
          H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2
        ∂pairLaw) := by
  let delta := fun z : Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
      H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2 center
  let energy := fun z : Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
      H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2
  have hEnergyNonneg : ∀ z, 0 ≤ energy z := by
    intro z
    dsimp [energy,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy]
    exact integral_nonneg fun g => sq_nonneg _
  have hPointwise : ∀ z, |delta z| ≤ Real.sqrt (energy z) := by
    intro z
    simpa [delta, energy,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdatedCenteredMean_direct_difference_le_sqrt_directDifferenceEnergy_of_bounded
        H N hN beta hbeta target source hne F hF bound hbound
        left B A retained distinguishedSource k g₂ z.1 z.2 center
  have hLift :=
    RealIntegralPointwiseRMSResponseL2.sqrt_integral_sq_le_mul_sqrt_integral_of_pointwise
      pairLaw delta energy 1
      (by simpa [delta] using hDeltaSq)
      (by simpa [energy] using hEnergy)
      hEnergyNonneg (by norm_num)
      (by
        intro z
        simpa using hPointwise z)
  simpa [delta, energy] using hLift

/-- Any majorant for the averaged direct energy immediately bounds the direct
pair-law L2 response amplitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdateDirectMeanDifference_pairL2_le_of_directEnergy_majorant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) (center amplitude : ℝ)
    (pairLaw : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ))
    (hDeltaSq : Integrable (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
        H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2 center ^ 2) pairLaw)
    (hEnergy : Integrable (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
        H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2) pairLaw)
    (hMajorant : Real.sqrt (∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
        H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2 ∂pairLaw) ≤ amplitude) :
    Real.sqrt (∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
        H N hN beta hbeta target source hne F left B A retained distinguishedSource k g₂ z.1 z.2 center ^ 2 ∂pairLaw) ≤ amplitude := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdateDirectMeanDifference_pairL2_le_directEnergy
      H N hN beta hbeta target source hne F hF bound hbound
      left B A retained distinguishedSource k g₂ center pairLaw hDeltaSq hEnergy).trans hMajorant

end

end MGAP4D.MathlibAnalytic
