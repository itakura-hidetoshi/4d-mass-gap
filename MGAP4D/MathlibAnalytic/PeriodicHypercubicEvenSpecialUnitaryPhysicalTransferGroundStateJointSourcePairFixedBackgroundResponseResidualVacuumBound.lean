import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseResidualCoefficient
import Mathlib.Tactic

/-!
# Vacuum integration of the fixed-background response-to-residual bound

PR #4843 proves at each fixed outer boundary C that the complete source-summed
fixed-background response-amplitude energy is bounded by

  rhoResp(s,beta) * sum_target E_target(C,target).

PR #4844 proves that rhoResp(s,beta) is finite on the canonical shell cutoff.
That finiteness is exactly what is needed to pull the constant coefficient
through the outer physical-vacuum lower integral without any measurability
hypothesis on the residual-energy sum.

This file performs only that outer integration step:

  integral_C ResponseEnergy(C)
    <= rhoResp(s,beta) * integral_C sum_target E_target(C,target).

The finite target sum is deliberately left inside the outer integral.  Its
exchange with the vacuum integral, and subsequent identification with the sum
of canonical target fiber variances, remains a separate theorem unit.

No finite-cardinality factor, new cutoff, response symmetry, or probability-law
replacement is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundResponseResidualVacuumBoundSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundResponseResidualVacuumBoundSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Vacuum integration of the fixed-C response-amplitude estimate, with the
finite response-to-residual coefficient pulled outside the outer lower
integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_targetResidualEnergySum_lintegral
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (∫⁻ C,
      ENNReal.ofReal
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
              H N hN beta hbeta C distinguishedSource
              (F target) (hF target) (bound target) (hbound target)
              source target) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        (∫⁻ C,
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
              H N hN beta hbeta C target (F target)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
  let rho : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
      s beta
  let targetEnergySum :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target (F target)
  have hRhoTop : rho ≠ ⊤ := by
    simpa [rho] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient_ne_top
        s hs beta hbeta hcut
  have hPoint :
      ∀ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
                H N hN beta hbeta C distinguishedSource
                (F target) (hF target) (bound target) (hbound target)
                source target) ^ 2) ≤
          rho * targetEnergySum C := by
    intro C
    simpa [rho, targetEnergySum] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_sum_sq_ofReal_le_responseResidualCoefficient_mul_targetResidualEnergy_sum
        N hN s hs beta hbeta hcut H C distinguishedSource
        F hF bound hbound
  calc
    (∫⁻ C,
      ENNReal.ofReal
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
              H N hN beta hbeta C distinguishedSource
              (F target) (hF target) (bound target) (hbound target)
              source target) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ∫⁻ C, rho * targetEnergySum C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta :=
      lintegral_mono hPoint
    _ =
      rho *
        (∫⁻ C, targetEnergySum C
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
      rw [lintegral_const_mul' rho targetEnergySum hRhoTop]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        (∫⁻ C,
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
              H N hN beta hbeta C target (F target)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
      rfl

end

end MGAP4D.MathlibAnalytic
