import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionRightUpdateTiltResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorSourceRatioLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance kernelSectionTwoSourceCrossingResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Changing one fixed right-boundary source from `k` to `h` changes the
kernel-section expectation of an arbitrary real observable by exactly the
covariance with the one-link Wilson crossing ratio, divided by the positive
mean of that crossing ratio under the `k`-section law.

The right-boundary spatial half-action ratio cancels from numerator and
denominator because it is independent of the left configuration.  Thus the
response is expressed using precisely the source observable that occurs in the
remote C5 covariance residual.  No decay, summability, or conditional-law
interpretation is asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_twoSource_integral_sub_eq_crossingRatio_covariance_div_expectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    (∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update B source h)) -
      (∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update B source k)) =
      realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta (Function.update B source k))
          (fun A =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h /
              specialUnitaryWilsonRelativeKernel N beta (A source) k)
          F /
        (∫ A,
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta (Function.update B source k)) := by
  classical
  let Ck : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B source k
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta Ck
  let r : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      specialUnitaryWilsonRelativeKernel N beta (A source) h /
        specialUnitaryWilsonRelativeKernel N beta (A source) k
  let c : ℝ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h /
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k
  have hCPos : 0 < c := by
    exact div_pos
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor_pos
        H N beta B source h)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor_pos
        H N beta B source k)
  have hUpdate : Function.update Ck source h = Function.update B source h := by
    funext e
    by_cases he : e = source
    · subst e
      simp [Ck]
    · simp [Ck, he]
  have hLocal :
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A Ck source h) =
        (fun A => c * r A) := by
    funext A
    have hKkPos :
        0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A Ck :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta A Ck
    have hFactor :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
        H N beta A Ck source h
    have hAsRatio :
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A Ck source h =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update Ck source h) /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A Ck := by
      apply (eq_div_iff (ne_of_gt hKkPos)).2
      exact hFactor.symm
    rw [hAsRatio, hUpdate]
    change
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (Function.update B source h) /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (Function.update B source k) =
        c * r A
    simpa [c, r] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_source_update_ratio_eq_spatialHalfUpdateFactor_ratio_mul_crossingRatio
        H N beta A B source h k)
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_update_right_sub_eq_covariance_div_localFactor_expectation
      H N hN beta hbeta Ck source h F
  rw [hUpdate] at hResponse
  have hMeanScale :
      (∫ A, c * r A ∂nu) = c * ∫ A, r A ∂nu := by
    exact integral_const_mul c r
  have hCovScale :
      realIntegralCovariance nu (fun A => c * r A) F =
        c * realIntegralCovariance nu r F := by
    unfold realIntegralCovariance
    have hJoint :
        (∫ A, (c * r A) * F A ∂nu) =
          c * ∫ A, r A * F A ∂nu := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with A
      ring
    rw [hJoint, hMeanScale]
    ring
  have hLocalMeanPos :
      0 <
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A Ck source h
          ∂nu := by
    change
      0 <
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A Ck source h
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta Ck
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_rightTargetLocalFactor_eq_vacuum_update_ratio
        H N hN beta hbeta Ck source h]
    exact div_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta (Function.update Ck source h))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta Ck)
  have hMeanRPos : 0 < ∫ A, r A ∂nu := by
    rw [hLocal, hMeanScale] at hLocalMeanPos
    nlinarith
  have hScaledResponse :
      (∫ A, F A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta (Function.update B source h)) -
        (∫ A, F A ∂nu) =
        realIntegralCovariance nu (fun A => c * r A) F /
          (∫ A, c * r A ∂nu) := by
    simpa [nu, Ck, hLocal] using hResponse
  rw [hCovScale, hMeanScale] at hScaledResponse
  have hCancel :
      (c * realIntegralCovariance nu r F) / (c * ∫ A, r A ∂nu) =
        realIntegralCovariance nu r F / (∫ A, r A ∂nu) := by
    field_simp [ne_of_gt hCPos, ne_of_gt hMeanRPos]
  rw [hCancel] at hScaledResponse
  simpa [nu, Ck, r] using hScaledResponse

end

end MathlibAnalytic
end MGAP4D
