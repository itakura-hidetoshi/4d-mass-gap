import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceProbability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFullKernelSectionBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionTwoSourceCrossingResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorPlaquetteSeparation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance referenceFixedRightTargetRatioResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The one-link Wilson crossing ratio has strictly positive mean under the
fixed-right continuous ground-state kernel-section probability law.

This is the positivity fact used internally by the two-source response theorem,
exposed here so that the covariance identity can be multiplied back into a
division-free response form. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_crossingRatio_integral_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      ∫ A,
        specialUnitaryWilsonRelativeKernel N beta (A source) h /
          specialUnitaryWilsonRelativeKernel N beta (A source) k
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update B source k) := by
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
  have hMeanScale :
      (∫ A, c * r A ∂nu) = c * ∫ A, r A ∂nu := by
    exact integral_const_mul c r
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
  simpa [nu, Ck, r] using hMeanRPos

/-- For a spatially remote target/source pair, the covariance appearing in the
normalized C5 reference law is exactly the positive source-crossing mean times
the fixed-right boundary response of the literal target-local ratio.

The reference law is first identified with the kernel section whose right
boundary is `B[source ← k][target ← g₂]`.  The two-source response theorem is
then applied at base `B[target ← g₂]`; the only transport needed is the explicit
commutation of the distinct target/source updates.  No Gibbs/RCD
identification, decay, summability, or contraction hypothesis is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_targetRatio_crossingRatio_covariance_eq_crossingRatioExpectation_mul_fixedRight_response_of_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂)
        (fun A =>
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k) =
      (∫ A,
        specialUnitaryWilsonRelativeKernel N beta (A source) h /
          specialUnitaryWilsonRelativeKernel N beta (A source) k
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂)) *
      ((∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source h) target g₂)) -
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))) := by
  classical
  let B₂ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B target g₂
  let F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂
  let r : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun A =>
      specialUnitaryWilsonRelativeKernel N beta (A source) h /
        specialUnitaryWilsonRelativeKernel N beta (A source) k
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
  have hReference :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
      H N hN beta hbeta B hne hNoShare k g₂
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_twoSource_integral_sub_eq_crossingRatio_covariance_div_expectation
      H N hN beta hbeta B₂ source h k F
  rw [hCommH, hCommK] at hResponse
  have hMeanPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_crossingRatio_integral_pos
      H N hN beta hbeta B₂ source h k
  rw [hCommK] at hMeanPos
  have hResponse' :
      (∫ A, F A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source h) target g₂)) -
        (∫ A, F A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) =
        realIntegralCovariance
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g₂))
            r F /
          (∫ A, r A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g₂)) := by
    simpa [F, r] using hResponse
  have hMeanPos' :
      0 <
        ∫ A, r A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂) := by
    simpa [r] using hMeanPos
  have hCovSymm :
      realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          F r =
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          r F := by
    unfold realIntegralCovariance
    have hJoint :
        (∫ A, F A * r A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) =
        ∫ A, r A * F A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂) := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    rw [hJoint]
    ring
  have hMul := (eq_div_iff (ne_of_gt hMeanPos')).mp hResponse'
  have hCovResponse :
      realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          r F =
        (∫ A, r A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) *
        ((∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source h) target g₂)) -
          (∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g₂))) := by
    calc
      realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          r F =
        ((∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source h) target g₂)) -
          (∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g₂))) *
        (∫ A, r A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) := hMul.symm
      _ =
        (∫ A, r A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) *
        ((∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source h) target g₂)) -
          (∫ A, F A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g₂))) := by ring
  rw [hReference]
  rw [hCovSymm]
  simpa [F, r] using hCovResponse

/-- The complete same-color remote physical cross-ratio defect is therefore an
explicit source spatial factor times the squared reference partition function,
times the positive crossing-ratio mean, times a fixed-right target-ratio
expectation response.

This is the exact response form needed before introducing a distance-sensitive
response kernel.  No coefficient is dropped or simplified. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_sameColor_remote_crossRatio_defect_eq_sourceSpatialRatio_mul_partition_sq_mul_crossingExpectation_mul_fixedRight_targetRatio_response
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H target =
      periodicHypercubicEvenSpatialSliceLinkColor H source)
    (hne : target ≠ source)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂)) -
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k) *
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction
          H N hN beta hbeta B target source k g₂) ^ 2 *
        ((∫ A,
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) *
        ((∫ A,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₂
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source h) target g₂)) -
          (∫ A,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₂
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g₂))))) := by
  have hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source := by
    rintro ⟨p, hTarget, hSource⟩
    exact hne
      (periodicHypercubicEvenSpatialSliceLink_sameColor_touches_eq
        H (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
        hTarget hSource hColor)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_sameColor_remote_crossRatio_defect_eq_sourceSpatialRatio_mul_partition_sq_mul_referenceProbabilityCovariance
      H N hN beta hbeta B (target := target) (source := source)
      hColor hne h k g₁ g₂]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_targetRatio_crossingRatio_covariance_eq_crossingRatioExpectation_mul_fixedRight_response_of_remote
      H N hN beta hbeta B (target := target) (source := source)
      hne hNoShare h k g₁ g₂]

end

end MathlibAnalytic
end MGAP4D