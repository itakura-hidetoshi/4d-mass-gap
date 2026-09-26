import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageDependentNormedResponseOuterLIntegralSchurReceiver
import Mathlib.Tactic

/-!
# A.e. source-dependent response assembly through the outer transpose Schur receiver

PR #4819 composes the source-dependent normed-response assembler with the
outer transpose Schur receiver when the decomposition and norm bounds hold at
every outer background.

The concrete localPart chain is naturally available only almost everywhere on
the relevant outer law: PR #4766 descends the canonical residual identity by
absolute continuity, and PR #4767 integrates that a.e. identity.

This file therefore weakens only the outer-background quantifier.  The exact
decomposition, local bound, and response bound are required simultaneously
for almost every background.  On that full-measure set the existing finite
dependent normed-response lemma gives the pointwise transpose recurrence, and
`lintegral_mono_ae` integrates it.

No response estimate, probability law, coefficient, cutoff, factor two, or
finite-cardinality factor is changed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

local instance aeDependentNormedResponseOuterSchurSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance aeDependentNormedResponseOuterSchurSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Almost-everywhere outer-background version of PR #4819.

The carrier may depend on both the outer background and the source link.
No common carrier across sources is required. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_aeDependentNormedResponse_outerLIntegralTransposeSchurReceiver
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
    (hDecomp :
      ∀ᵐ A ∂μ, ∀ source,
        state A source =
          localPart A source + ∑ target, response A source target)
    (hLocal :
      ∀ᵐ A ∂μ, ∀ source,
        ‖localPart A source‖ ≤ localProfile A source)
    (hResponse :
      ∀ᵐ A ∂μ, ∀ source target,
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
  apply lintegral_mono_ae
  filter_upwards [hDecomp, hLocal, hResponse] with A hDecompA hLocalA hResponseA
  apply ENNReal.ofReal_le_ofReal
  have hLocalNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤ localProfile A e := by
    intro e
    exact (norm_nonneg (localPart A e)).trans (hLocalA e)
  have hOneSided :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖state A source‖ ≤
          localProfile A source +
            ∑ target,
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A).influence target source *
                ‖state A target‖ := by
    exact
      FiniteDependentNormedTransposeResponseProfile.norm_profile_transpose_oneSided
        (E A)
        (fun target source =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source)
        (state A) (localPart A) (response A) (localProfile A)
        hDecompA hLocalA hResponseA
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_oneSided_global_energy_coercive_uniform
      N hN s hs beta hbeta hcut H A
      (fun e => ‖state A e‖) (localProfile A)
      (fun e => norm_nonneg (state A e))
      hLocalNonneg hOneSided

/-- Physical-vacuum specialization of the a.e. dependent-response outer
transpose Schur assembly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_aeDependentNormedResponse_vacuumLIntegralTransposeSchurReceiver
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
    (hDecomp :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta,
        ∀ source,
          state A source =
            localPart A source + ∑ target, response A source target)
    (hLocal :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta,
        ∀ source,
          ‖localPart A source‖ ≤ localProfile A source)
    (hResponse :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta,
        ∀ source target,
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_aeDependentNormedResponse_outerLIntegralTransposeSchurReceiver
      N hN s hs beta hbeta hcut H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)
      E state localPart response localProfile
      hDecomp hLocal hResponse

end

end MGAP4D.MathlibAnalytic
