import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageFullEnvelopeRMSCauchy
import Mathlib.Tactic

/-!
# Source-indexed RMS majorant interface for the full physical envelope

PR #4711 proves source-uniform full-envelope centered RMS transport for one
canonical bounded-concrete sweep-stage representative.  Its right-hand RMS
factor is still a target-section conditional second moment.  The Schur
receiver, however, needs the source-indexed profile value u(source).

This file makes that missing comparison explicit instead of identifying the
indices by notation.  A source RMS majorant is precisely a profile u for which

  sqrt(E_target,source(uValue) + E_target,source(vValue)) <= u source

for every off-diagonal source and every two source-link values.  Combining
this premise with the #4711 full-K transport gives exactly

  |Delta_target,source| <= K(target,source) * u source.

Thus the only remaining trajectory task is to construct such a source-indexed
RMS majorant from the canonical sweep/hybrid geometry.  No new coefficient or
volume factor is introduced here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

local instance sourceRMSMajorantSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceRMSMajorantSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceRMSMajorantSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceRMSMajorantSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceRMSMajorantSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourceRMSMajorantSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact source-indexed RMS majorant required to turn the #4711
source-uniform full-K centered-mean estimate into the Schur orientation
K(target,source) * profile(source). -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceRMSMajorizedBy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) (center : ℝ)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) : Prop :=
  ∀ (source : PeriodicHypercubicEvenSpatialSliceLink H),
    target ≠ source →
    ∀ (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
      Real.sqrt
          ((∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N target F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B source distinguishedSource target k g₂
                (Function.update A source u)) +
            ∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N target F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B source distinguishedSource target k g₂
                (Function.update A source v)) ≤
        profile source

/-- The corresponding source-oriented centered-mean response bound. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceResponseBoundedBy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) (center : ℝ)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) : Prop :=
  ∀ (source : PeriodicHypercubicEvenSpatialSliceLink H),
    target ≠ source →
    ∀ (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |(∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂
            (Function.update A source u)) -
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂
            (Function.update A source v))| ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile source

/-- Full-envelope centered RMS transport plus a source-indexed RMS majorant
gives exactly the source-oriented K * profile response needed by the Schur
recurrence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceResponse_le_envelope_mul_profile_of_fullEnvelopeRMS_and_sourceRMSMajorant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) (center : ℝ)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hFull :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionFullEnvelopeCenteredRMS
        H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center)
    (hMajorant :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceRMSMajorizedBy
        H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center profile) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceResponseBoundedBy
      H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center profile := by
  intro source hne u v
  have hTransport := hFull source hne u v
  have hEnergy := hMajorant source hne u v
  have hKNonneg :
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A).influence_nonneg target source
  exact hTransport.trans (mul_le_mul_of_nonneg_left hEnergy hKNonneg)

/-- Canonical sweep-stage form: one representative is chosen once.  For every
candidate source profile, proving the source RMS majorant for that same
representative immediately yields the exact K(target,source) * profile(source)
response bound while retaining the sharp Haar local certificate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaar_fullEnvelope_and_sourceMajorant_interface
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (color : PeriodicHypercubicEvenGroundStateSpatialColor) (stage : ℕ)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H e.1 → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) (center : ℝ) :
    ∃ (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2 H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector H N hN beta hbeta color
          (((Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage) f ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional H N hN beta hbeta e.1 F ≤
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector H N hN beta hbeta color
              (((Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage) f -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2 H N hN beta hbeta color e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector H N hN beta hbeta color
                (((Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage) f)‖ ^ 2) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionFullEnvelopeCenteredRMS
        H N hN beta hbeta e.1 F left B A retained distinguishedSource k g₂ center ∧
      ∀ profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceRMSMajorizedBy
            H N hN beta hbeta e.1 F left B A retained distinguishedSource k g₂ center profile →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceResponseBoundedBy
            H N hN beta hbeta e.1 F left B A retained distinguishedSource k g₂ center profile := by
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaar_and_fullEnvelope_centeredRMS
        N hN s hs beta hbeta hcut H color stage e f hf
        left B A retained distinguishedSource k g₂ center with
    ⟨F, hF, bound, hbound, hRep, hSharp, hFull⟩
  refine ⟨F, hF, bound, hbound, hRep, hSharp, hFull, ?_⟩
  intro profile hMajorant
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceResponse_le_envelope_mul_profile_of_fullEnvelopeRMS_and_sourceRMSMajorant
      H N hN beta hbeta e.1 F left B A retained distinguishedSource k g₂ center
      profile hFull hMajorant

end

end MGAP4D.MathlibAnalytic
