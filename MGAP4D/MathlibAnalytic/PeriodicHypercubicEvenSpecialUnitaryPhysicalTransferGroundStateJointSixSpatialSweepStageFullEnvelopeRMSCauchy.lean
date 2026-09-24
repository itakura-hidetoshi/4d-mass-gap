import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageActiveEnvelopeRMSCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteRemoteEnvelopeRMSCauchy
import Mathlib.Tactic

/-!
# Full-envelope centered RMS transport at canonical ground-state sweep stages

The preceding theorem units close the two pointwise sectors separately:

* active source links: the local physical Harnack coefficient is bounded by the
  actual full physical envelope entry;
* non-active off-diagonal source links: the physical remote cross-ratio RMS
  estimate has exactly the source-aligned remote envelope entry.

This file chooses the canonical bounded-concrete sweep-stage representative
only once and proves that the same representative satisfies the actual full-K
centered RMS estimate for every off-diagonal source link.  Thus the
active/remote split is internal to the proof and downstream trajectory/profile
assembly sees only K(target,source).
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

local instance stagewiseFullEnvelopeRMSFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Full physical-envelope centered RMS transport for one bounded concrete
section at a fixed target link. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionFullEnvelopeCenteredRMS
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) (center : ℝ) : Prop :=
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
            H N hN beta hbeta A).influence target source *
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
                  (Function.update A source v))

/-- Every canonical fixed-color sweep prefix admits one bounded representative
which simultaneously carries the sharp Haar residual certificate and the
actual full-envelope centered RMS transport for every off-diagonal source.

Crucially, the representative is chosen before the source link is quantified;
there is no source-dependent reselection of the L2 representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaar_and_fullEnvelope_centeredRMS
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
        H N hN beta hbeta e.1 F left B A retained distinguishedSource k g₂ center := by
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaarVariance_le_residual
        H N hN beta hbeta color stage e f hf with
    ⟨F, hF, bound, hbound, hRep, hSharp⟩
  refine ⟨F, hF, bound, hbound, hRep, hSharp, ?_⟩
  intro source hne u v
  by_cases hActive :
      e.1 ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
  · have hLocal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_backgroundUpdate_centered_integral_sub_abs_le_harnackInfluence_mul_sqrt_energy_of_bounded
        H N hN beta hbeta e.1 F hF bound hbound
        left retained B A source distinguishedSource source hne
        k g₂ u v center
    have hCoeff :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_le_physicalLeftInfluenceEnvelopeKernel_of_active
        H N hN beta hbeta A source e.1 hActive
    have hSqrt : 0 ≤
        Real.sqrt
          ((∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N e.1 F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B source distinguishedSource e.1 k g₂
                (Function.update A source u)) +
            ∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N e.1 F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B source distinguishedSource e.1 k g₂
                (Function.update A source v)) :=
      Real.sqrt_nonneg _
    exact hLocal.trans (mul_le_mul_of_nonneg_right hCoeff hSqrt)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceAlignedRemote_centered_integral_sub_abs_le_envelopeKernel_mul_sqrt_energy_of_bounded
        N hN s hs beta hbeta hcut H e.1 source hne hActive
        F hF bound hbound left B A retained distinguishedSource
        k g₂ u v center

end

end MGAP4D.MathlibAnalytic
