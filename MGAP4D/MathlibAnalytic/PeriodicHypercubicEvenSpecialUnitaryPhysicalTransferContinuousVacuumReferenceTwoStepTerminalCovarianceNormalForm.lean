import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalResidualCertificate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionTwoSourceCrossingResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance twoStepTerminalCovarianceNormalFormSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The two-step-smoothed target-ratio observable appearing in the terminal
response. Naming it makes the remaining nonlocal obstruction visible without
changing its carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
    H N hN beta hbeta B target source g₂ k
    (fun C =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g₂)
    2 A

/-- The exact two-step terminal response is a single covariance under the
fixed-k kernel-section law, divided by the positive mean of the source crossing
ratio.

No Gibbs/RCD identification, spatial decay, summability, or contraction is
used here. The only geometric input is that target and source are distinct, so
their right-boundary updates commute. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs_eq_abs_covariance_div_crossingExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k =
      |realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          (fun A =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h /
              specialUnitaryWilsonRelativeKernel N beta (A source) k)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
            H N hN beta hbeta B target source g₁ g₂ k) /
        (∫ A,
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))| := by
  let B₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B target g₂
  let F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
      H N hN beta hbeta B target source g₁ g₂ k
  have hCommH :
      Function.update B₂ source h =
        Function.update (Function.update B source h) target g₂ := by
    funext e
    by_cases hTarget : e = target
    · subst e
      simp [B₂, hne, Ne.symm hne]
    · by_cases hSource : e = source
      · subst e
        simp [B₂, hne, Ne.symm hne]
      · simp [B₂, hTarget, hSource]
  have hCommK :
      Function.update B₂ source k =
        Function.update (Function.update B source k) target g₂ := by
    funext e
    by_cases hTarget : e = target
    · subst e
      simp [B₂, hne, Ne.symm hne]
    · by_cases hSource : e = source
      · subst e
        simp [B₂, hne, Ne.symm hne]
      · simp [B₂, hTarget, hSource]
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_twoSource_integral_sub_eq_crossingRatio_covariance_div_expectation
      H N hN beta hbeta B₂ source h k F
  rw [hCommH, hCommK] at hResponse
  have hAbs := congrArg abs hResponse
  simpa [
    F,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs] using hAbs

/-- The crossing-ratio denominator in the terminal covariance normal form is
strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalCrossingExpectation_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      ∫ A,
        specialUnitaryWilsonRelativeKernel N beta (A source) h /
          specialUnitaryWilsonRelativeKernel N beta (A source) k
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂) := by
  let B₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B target g₂
  have hCommK :
      Function.update B₂ source k =
        Function.update (Function.update B source k) target g₂ := by
    funext e
    by_cases hTarget : e = target
    · subst e
      simp [B₂, hne, Ne.symm hne]
    · by_cases hSource : e = source
      · subst e
        simp [B₂, hne, Ne.symm hne]
      · simp [B₂, hTarget, hSource]
  have hPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_crossingRatio_integral_pos
      H N hN beta hbeta B₂ source h k
  rw [hCommK] at hPos
  exact hPos

/-- Therefore the terminal response is the covariance absolute value divided by
a strictly positive scalar, with no absolute value left on the denominator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs_eq_abs_covariance_div_pos_crossingExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k =
      |realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          (fun A =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h /
              specialUnitaryWilsonRelativeKernel N beta (A source) k)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalObservable
            H N hN beta hbeta B target source g₁ g₂ k)| /
        (∫ A,
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalResponseAbs_eq_abs_covariance_div_crossingExpectation
      H N hN beta hbeta B hne g₁ g₂ h k,
    abs_div,
    abs_of_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioTwoStepTerminalCrossingExpectation_pos
        H N hN beta hbeta B hne g₂ h k)]

end

end MathlibAnalytic
end MGAP4D
