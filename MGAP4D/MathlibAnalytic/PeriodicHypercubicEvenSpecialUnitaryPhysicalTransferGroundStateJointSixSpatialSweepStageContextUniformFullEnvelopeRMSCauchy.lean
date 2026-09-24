import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageFullEnvelopeRMSCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteRemoteEnvelopeRMSCauchy
import Mathlib.Tactic

/-!
# Context-uniform full-envelope RMS transport at canonical sweep stages

PR #4711 proved the full physical-envelope centered RMS estimate for a
canonical bounded-concrete sweep-stage representative after fixing one
left/right/background context.

The representative supplied by the sharp-Haar stage theorem is actually
chosen independently of all those contexts.  The local active and remote RMS
theorems are likewise valid for arbitrary contexts.  This file exposes that
stronger quantifier order:

  exists F_stage, for every context and every off-diagonal source,
    centered mean transport <= K(target,source) * RMS energy.

This is the quantifier order required by a hybrid/trajectory construction,
where one fixed concrete representative must be reused while the background
configuration changes.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

local instance contextUniformFullEnvelopeRMSIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance contextUniformFullEnvelopeRMSCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance contextUniformFullEnvelopeRMSSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance contextUniformFullEnvelopeRMSMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance contextUniformFullEnvelopeRMSBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance contextUniformFullEnvelopeRMSSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Any bounded strongly measurable concrete section satisfies the
source-uniform full physical-envelope centered RMS estimate on the strict
physical-sweep interval.  This is the context-free engine hidden inside the
stage-specific theorem of PR #4711. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_fullEnvelopeCenteredRMS_of_bounded
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionFullEnvelopeCenteredRMS
      H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center := by
  intro source hne u v
  by_cases hActive :
      target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
  · have hLocal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_backgroundUpdate_centered_integral_sub_abs_le_harnackInfluence_mul_sqrt_energy_of_bounded
        H N hN beta hbeta target F hF bound hbound
        left retained B A source distinguishedSource source hne
        k g₂ u v center
    have hCoeff :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_le_physicalLeftInfluenceEnvelopeKernel_of_active
        H N hN beta hbeta A source target hActive
    have hSqrt : 0 ≤
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
                (Function.update A source v)) :=
      Real.sqrt_nonneg _
    exact hLocal.trans (mul_le_mul_of_nonneg_right hCoeff hSqrt)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceAlignedRemote_centered_integral_sub_abs_le_envelopeKernel_mul_sqrt_energy_of_bounded
        N hN s hs beta hbeta hcut H target source hne hActive
        F hF bound hbound left B A retained distinguishedSource
        k g₂ u v center

/-- A canonical sweep-stage representative can be chosen once and for all
contexts.  It simultaneously realizes the genuine L2 stage vector, carries
the sharp Haar local certificate, and satisfies the actual full-K centered RMS
transport for every choice of outer context, retained off-target background,
fiber-law parameters, center and off-diagonal source link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaar_and_contextUniform_fullEnvelope_centeredRMS
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (stage : ℕ)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
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
      ∀
        (left B A :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (retained :
          PeriodicHypercubicEvenSpatialSliceOffTargetLink H e.1 →
            Matrix.specialUnitaryGroup (Fin N) ℂ)
        (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
        (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
        (center : ℝ),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionFullEnvelopeCenteredRMS
          H N hN beta hbeta e.1 F left B A retained distinguishedSource k g₂ center := by
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaarVariance_le_residual
        H N hN beta hbeta color stage e f hf with
    ⟨F, hF, bound, hbound, hRep, hSharp⟩
  refine ⟨F, hF, bound, hbound, hRep, hSharp, ?_⟩
  intro left B A retained distinguishedSource k g₂ center
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_fullEnvelopeCenteredRMS_of_bounded
      N hN s hs beta hbeta hcut H e.1
      F hF bound hbound left B A retained distinguishedSource k g₂ center

end

end MGAP4D.MathlibAnalytic
