import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonVacuumMeasure
import Mathlib.Tactic

/-!
# Outer-lintegral receiver for the background-dependent physical Schur estimate

The physical influence envelope depends on the outer background configuration
`A`.  Its row and column bounds, however, are already uniform in `A` on the
strict high-temperature interval.

Therefore the sharp route is not to replace the physical matrix by a coarser
configuration-independent kernel.  Instead, apply the existing one-sided
Schur theorem pointwise at every outer background and then integrate the
resulting nonnegative energy inequality.

This file packages exactly that step in `ENNReal` lower-integral form.  The
statement deliberately imposes no measurability or integrability assumptions
on the profile fields: `lintegral_mono` only needs the pointwise inequality.
Later physical modules may substitute their already-measurable section-energy
fields without reopening the Schur argument.

No new coefficient, response estimate, cardinality factor, or probability-law
identification is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

local instance outerLIntegralSchurReceiverSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance outerLIntegralSchurReceiverSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise physical one-sided Schur coercivity integrates over an arbitrary
outer measure with the same uniform coefficient.

The matrix remains the actual background-dependent physical envelope
`K_A(target,source)`; only its already-proved Schur coefficient is uniform. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_outerLIntegralSchurReceiver
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (μ :
      Measure
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (profile localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ A e, 0 ≤ profile A e)
    (hLocalNonneg : ∀ A e, 0 ≤ localProfile A e)
    (hOneSided : ∀ A target,
      profile A target ≤
        localProfile A target +
          ∑ source,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile A source) :
    (∫⁻ A,
      ENNReal.ofReal
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            profile A e ^ 2)
      ∂μ) ≤
      ∫⁻ A,
        ENNReal.ofReal
          (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            localProfile A e ^ 2)
        ∂μ := by
  apply lintegral_mono
  intro A
  apply ENNReal.ofReal_le_ofReal
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_oneSided_global_energy_coercive_uniform
      N hN s hs beta hbeta hcut H A
      (profile A) (localProfile A)
      (hProfileNonneg A) (hLocalNonneg A)
      (hOneSided A)

/-- Physical-vacuum specialization of the outer-lintegral Schur receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_vacuumLIntegralSchurReceiver
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (profile localProfile :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ A e, 0 ≤ profile A e)
    (hLocalNonneg : ∀ A e, 0 ≤ localProfile A e)
    (hOneSided : ∀ A target,
      profile A target ≤
        localProfile A target +
          ∑ source,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile A source) :
    (∫⁻ A,
      ENNReal.ofReal
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            profile A e ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ∫⁻ A,
        ENNReal.ofReal
          (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            localProfile A e ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_outerLIntegralSchurReceiver
      N hN s hs beta hbeta hcut H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)
      profile localProfile hProfileNonneg hLocalNonneg hOneSided

end

end MathlibAnalytic
end MGAP4D
