import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageTransposeSchurReceiver
import Mathlib.Tactic

/-!
# Outer-lintegral receiver for the background-dependent physical Schur estimate

The physical influence envelope depends on the outer background configuration
`A`, while its row and column bounds are already uniform in `A` on the
strict high-temperature interval.  The sharp route is therefore to apply the
existing one-sided Schur theorem pointwise and integrate the resulting
nonnegative energy inequality.

The receiver is stated directly in `ENNReal` lower-integral form.  No extra
measurability or integrability premise is needed for monotonicity itself.

No new coefficient, response estimate, cardinality factor, or probability-law
identification is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

local instance outerLIntegralSchurReceiverSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance outerLIntegralSchurReceiverSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise physical one-sided Schur coercivity integrates over an arbitrary
outer measure with the same uniform coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_outerLIntegralSchurReceiver
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ)
    (μ : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (profile localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ A e, 0 ≤ profile A e)
    (hLocalNonneg : ∀ A e, 0 ≤ localProfile A e)
    (hOneSided : ∀ A target,
      profile A target ≤ localProfile A target +
        ∑ source,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile A source) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile A e ^ 2) ∂μ) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile A e ^ 2) ∂μ := by
  apply lintegral_mono
  intro A
  apply ENNReal.ofReal_le_ofReal
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_oneSided_global_energy_coercive_uniform
      N hN s hs beta hbeta hcut H A
      (profile A) (localProfile A)
      (hProfileNonneg A) (hLocalNonneg A) (hOneSided A)

/-- Physical-vacuum specialization of the outer-lintegral Schur receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_vacuumLIntegralSchurReceiver
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ)
    (profile localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ A e, 0 ≤ profile A e)
    (hLocalNonneg : ∀ A e, 0 ≤ localProfile A e)
    (hOneSided : ∀ A target,
      profile A target ≤ localProfile A target +
        ∑ source,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile A source) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile A e ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile A e ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_outerLIntegralSchurReceiver
      N hN s hs beta hbeta hcut H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)
      profile localProfile hProfileNonneg hLocalNonneg hOneSided

/-- Transpose-oriented pointwise Schur coercivity integrates over an arbitrary
outer measure with the same uniform coefficient.  This is the orientation
consumed by the source-dependent response assembler. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_outerLIntegralTransposeSchurReceiver
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ)
    (μ : Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (profile localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ A e, 0 ≤ profile A e)
    (hLocalNonneg : ∀ A e, 0 ≤ localProfile A e)
    (hOneSided : ∀ A source,
      profile A source ≤ localProfile A source +
        ∑ target,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile A target) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile A e ^ 2) ∂μ) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile A e ^ 2) ∂μ := by
  apply lintegral_mono
  intro A
  apply ENNReal.ofReal_le_ofReal
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_oneSided_global_energy_coercive_uniform
      N hN s hs beta hbeta hcut H A
      (profile A) (localProfile A)
      (hProfileNonneg A) (hLocalNonneg A) (hOneSided A)

/-- Physical-vacuum specialization of the transpose outer-lintegral receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_vacuumLIntegralTransposeSchurReceiver
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ)
    (profile localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ A e, 0 ≤ profile A e)
    (hLocalNonneg : ∀ A e, 0 ≤ localProfile A e)
    (hOneSided : ∀ A source,
      profile A source ≤ localProfile A source +
        ∑ target,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * profile A target) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile A e ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile A e ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_outerLIntegralTransposeSchurReceiver
      N hN s hs beta hbeta hcut H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)
      profile localProfile hProfileNonneg hLocalNonneg hOneSided

end

end MathlibAnalytic
end MGAP4D
