import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageBackgroundUpdateRMSCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
import Mathlib.Tactic

/-!
# Active-neighbor sweep-stage RMS transport with the actual physical envelope

PR #4706 places the canonical bounded-concrete sweep-stage representative
inside the actual physical centered RMS background-update theorem.  Its local
coefficient is the already-canonical BackgroundUpdateHarnackInfluence(beta).

The full physical envelope kernel is the sum of that local Harnack term on
intrinsic active neighbors and the nonnegative source-aligned remote residual.
Hence, on an active target/source pair, the same local RMS estimate is
automatically controlled by the actual full envelope entry K(target,source).

This theorem unit performs exactly that promotion.  No new matrix coefficient
or volume-dependent factor is introduced.  The remote/non-active case remains
separate and will be handled by the cross-ratio/resolvent RMS route.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

local instance activeEnvelopeRMSCauchySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance activeEnvelopeRMSCauchySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance activeEnvelopeRMSCauchySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance activeEnvelopeRMSCauchySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance activeEnvelopeRMSCauchySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance activeEnvelopeRMSCauchySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- On an intrinsic active target/source pair, the local background-update
Harnack coefficient is bounded by the corresponding entry of the actual full
physical influence envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_le_physicalLeftInfluenceEnvelopeKernel_of_active
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hActive :
      target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source := by
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta ≤
      (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta
      else 0) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source target
  rw [if_pos hActive]
  exact
    le_add_of_nonneg_right
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
        H N hN beta hbeta A source target)

/-- At a canonical bounded-concrete sweep stage, every active background-link
update is controlled in centered RMS by the actual full physical envelope
entry K(target,source), while retaining the same representative and sharp Haar
residual certificate from PR #4706. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaar_and_activeEnvelope_centeredRMS
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (stage : ℕ)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H e.1 →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hActive :
      e.1 ∈
        periodicHypercubicEvenSpatialSliceActiveNeighbors H backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) :
    ∃
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color
          (((Finset.univ :
            Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage)
          f ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
          H N hN beta hbeta e.1 F ≤
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                H N hN beta hbeta color
                (((Finset.univ :
                  Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage)
                f -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta color e
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                  H N hN beta hbeta color
                  (((Finset.univ :
                    Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage)
                  f)‖ ^ 2) ∧
      |(∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N e.1 F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
            (Function.update A backgroundFiber u)) -
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N e.1 F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
            (Function.update A backgroundFiber v))| ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence e.1 backgroundFiber *
          Real.sqrt
            ((∫ g,
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                    H N e.1 F left retained g - center) ^ 2
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                  H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
                  (Function.update A backgroundFiber u)) +
              ∫ g,
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                    H N e.1 F left retained g - center) ^ 2
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                  H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
                  (Function.update A backgroundFiber v)) := by
  have hNotSelf :
      e.1 ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H e.1 := by
    simp [periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff]
  have hDistinct : e.1 ≠ backgroundFiber := by
    intro hEq
    subst backgroundFiber
    exact hNotSelf hActive
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaar_and_backgroundUpdate_centeredRMS
        H N hN beta hbeta color stage e f hf left retained B A
        distinguishedTarget distinguishedSource backgroundFiber hDistinct
        k g₂ u v center with
    ⟨F, hF, bound, hbound, hRep, hSharp, hRMS⟩
  refine ⟨F, hF, bound, hbound, hRep, hSharp, ?_⟩
  have hCoeff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_le_physicalLeftInfluenceEnvelopeKernel_of_active
      H N hN beta hbeta A backgroundFiber e.1 hActive
  have hSqrt :
      0 ≤
        Real.sqrt
          ((∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N e.1 F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
                (Function.update A backgroundFiber u)) +
            ∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N e.1 F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
                (Function.update A backgroundFiber v)) :=
    Real.sqrt_nonneg _
  exact hRMS.trans (mul_le_mul_of_nonneg_right hCoeff hSqrt)

end

end MGAP4D.MathlibAnalytic
