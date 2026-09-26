import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageDependentNormedResponseAssembler
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageOuterLIntegralSchurReceiver
import Mathlib.Tactic

/-!
# Source-dependent response assembly through the outer transpose Schur receiver

PR #4723 proves that, for each fixed physical background, an exact decomposition

  state_source = localPart_source + sum_target response_source,target

inside a source-dependent family of normed spaces yields the transpose-oriented
one-sided norm recurrence whenever

  ||response_source,target||
    <= K_A(target,source) * ||state_target||.

PR #4773 proves that this scalar recurrence may then be integrated over an
arbitrary outer background law while retaining the same uniform physical Schur
coefficient.

This file composes those two already-validated layers without identifying the
source-dependent carriers for different sources or backgrounds.  In particular
the physical background-dependent kernel K_A is retained exactly; it is not
replaced by the later configuration-independent pin-free kernel.

No new response estimate, cutoff, probability-law identification, factor two,
or cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

local instance dependentNormedResponseOuterSchurSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance dependentNormedResponseOuterSchurSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise source-dependent normed response decompositions feed directly
through the transpose outer-`lintegral` Schur receiver.

The normed carrier may depend on both the outer background `A` and the source
link.  Thus no common L2 carrier is imposed across different backgrounds or
sources. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_dependentNormedResponse_outerLIntegralTransposeSchurReceiver
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (μ :
      Measure
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (E :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → Type*)
    [∀ A e, NormedAddCommGroup (E A e)]
    (state localPart : ∀ A e, E A e)
    (response : ∀ A source target, E A source)
    (localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hDecomp : ∀ A source,
      state A source =
        localPart A source + ∑ target, response A source target)
    (hLocal : ∀ A source,
      ‖localPart A source‖ ≤ localProfile A source)
    (hResponse : ∀ A source target,
      ‖response A source target‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source *
          ‖state A target‖) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖state A e‖ ^ 2) ∂μ) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          localProfile A e ^ 2) ∂μ := by
  have hLocalNonneg : ∀ A e, 0 ≤ localProfile A e := by
    intro A e
    exact (norm_nonneg (localPart A e)).trans (hLocal A e)
  have hOneSided : ∀ A source,
      ‖state A source‖ ≤
        localProfile A source +
          ∑ target,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              ‖state A target‖ := by
    intro A
    exact
      FiniteDependentNormedTransposeResponseProfile.norm_profile_transpose_oneSided
        (E A)
        (fun target source =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source)
        (state A) (localPart A) (response A) (localProfile A)
        (hDecomp A) (hLocal A) (hResponse A)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_outerLIntegralTransposeSchurReceiver
      N hN s hs beta hbeta hcut H μ
      (fun A e => ‖state A e‖) localProfile
      (fun A e => norm_nonneg (state A e))
      hLocalNonneg hOneSided

/-- Physical-vacuum specialization of the source-dependent response assembly
through the outer transpose Schur receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_dependentNormedResponse_vacuumLIntegralTransposeSchurReceiver
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (E :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → Type*)
    [∀ A e, NormedAddCommGroup (E A e)]
    (state localPart : ∀ A e, E A e)
    (response : ∀ A source target, E A source)
    (localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hDecomp : ∀ A source,
      state A source =
        localPart A source + ∑ target, response A source target)
    (hLocal : ∀ A source,
      ‖localPart A source‖ ≤ localProfile A source)
    (hResponse : ∀ A source target,
      ‖response A source target‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source *
          ‖state A target‖) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖state A e‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          localProfile A e ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_dependentNormedResponse_outerLIntegralTransposeSchurReceiver
      N hN s hs beta hbeta hcut H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)
      E state localPart response localProfile
      hDecomp hLocal hResponse

end

end MGAP4D.MathlibAnalytic
