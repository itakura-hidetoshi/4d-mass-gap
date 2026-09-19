import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanBlockIterateBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceTelescope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFullKernelSectionBridge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

local instance referenceRestrictedRandomScanCovarianceSubsequenceLimitSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanCovarianceSubsequenceLimitSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanCovarianceSubsequenceLimitSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanCovarianceSubsequenceLimitSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanCovarianceSubsequenceLimitSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanCovarianceSubsequenceLimitSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Along the complete-block subsequence, the covariance remainder in the
original observable-level restricted random-scan telescope converges to zero.

This is a fixed-volume consequence of the exact block/one-step bridge and the
Doeblin stationary block limit.  The stationary reference probability measure
is identified exactly with the remote fixed-right ground-state kernel-section
probability law before the covariance estimate is taken. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_mul_scheduleLength_tendsto_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (g₂ k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hGStrong : StronglyMeasurable G)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)))
    (hG : MemLp G 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)))
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |G X - G Y| ≤ R) :
    Tendsto
      (fun n : ℕ =>
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k G
            (n *
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
                H).length)))
      atTop (𝓝 0) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  let μref :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let L :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length
  let rho :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta).toReal
  let c := ∫ X, G X ∂μref
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)
  have hMeasure : μref = μ := by
    dsimp [μref, μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
        H N hN beta hbeta B hne hNoShare k g₂
  have hFInt : Integrable F μ :=
    memLp_one_iff_integrable.1 (hF.mono_exponent one_le_two)
  have hAbsFInt : Integrable (fun X => |F X|) μ := by
    simpa [Real.norm_eq_abs] using hFInt.norm
  have hBound :
      ∀ n : ℕ,
        |realIntegralCovariance μ F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k G (n * L))| ≤
          (rho ^ n * R) * (∫ X, |F X| ∂μ) := by
    intro n
    let Gn :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g₂ k G (n * L)
    have hGn :
        MemLp Gn 2 μ := by
      dsimp [Gn, μ, L]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScanExpectationIterate_memLp_two
          H N hN beta hbeta B hne hNoShare g₂ k G hG
          (n *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length)
    have hFGnInt : Integrable (fun X => F X * Gn X) μ :=
      hF.integrable_mul hGn
    have hMean : (∫ X, Gn X ∂μ) = c := by
      rw [← hMeasure]
      dsimp [c]
      have hBridge :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
              H N hN beta hbeta B target source k g₂ G n =
            Gn := by
        funext A
        dsimp [Gn, L]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_eq_expectationIterate_mul_scheduleLength
            H N hN beta hbeta B target source k g₂ G hGStrong R hR hOsc n A
      rw [← hBridge]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_integral_referenceProbabilityMeasure_eq
          H N hN beta hbeta B target source k g₂ G hGStrong R hR hOsc n
    have hCentered :
        ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          |Gn A - c| ≤ rho ^ n * R := by
      intro A
      dsimp [Gn, c, rho, L]
      rw [
        ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_eq_expectationIterate_mul_scheduleLength
          H N hN beta hbeta B target source k g₂ G hGStrong R hR hOsc n A]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_sub_referenceMean_abs_le
          H N hN beta hbeta B target source k g₂ G hGStrong R hR hOsc n A
    have hFcInt : Integrable (fun X => F X * c) μ := by
      simpa [mul_comm] using hFInt.const_mul c
    have hCenteredProductInt :
        Integrable (fun X => F X * (Gn X - c)) μ := by
      have h := hFGnInt.sub hFcInt
      simpa [mul_sub] using h
    have hAbsCenteredProductInt :
        Integrable (fun X => |F X * (Gn X - c)|) μ :=
      hCenteredProductInt.abs
    have hMajorInt :
        Integrable (fun X => (rho ^ n * R) * |F X|) μ :=
      hAbsFInt.const_mul (rho ^ n * R)
    have hCenteredIntegral :
        (∫ X, F X * (Gn X - c) ∂μ) =
          (∫ X, F X * Gn X ∂μ) - (∫ X, F X ∂μ) * c := by
      calc
        (∫ X, F X * (Gn X - c) ∂μ) =
            ∫ X, (F X * Gn X) - (F X * c) ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun X => by ring
        _ = (∫ X, F X * Gn X ∂μ) - ∫ X, F X * c ∂μ := by
              rw [integral_sub hFGnInt hFcInt]
        _ = (∫ X, F X * Gn X ∂μ) - (∫ X, F X ∂μ) * c := by
              rw [integral_mul_const]
    change |realIntegralCovariance μ F Gn| ≤ _
    unfold realIntegralCovariance
    rw [hMean, ← hCenteredIntegral]
    calc
      |∫ X, F X * (Gn X - c) ∂μ| ≤
          ∫ X, |F X * (Gn X - c)| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ X, (rho ^ n * R) * |F X| ∂μ := by
        apply integral_mono hAbsCenteredProductInt hMajorInt
        intro X
        rw [abs_mul]
        calc
          |F X| * |Gn X - c| ≤ |F X| * (rho ^ n * R) :=
            mul_le_mul_of_nonneg_left (hCentered X) (abs_nonneg _)
          _ = (rho ^ n * R) * |F X| := by ring
      _ = (rho ^ n * R) * (∫ X, |F X| ∂μ) := by
        rw [integral_const_mul]
  have hPow :
      Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0) := by
    dsimp [rho]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_toReal_pow_tendsto_zero
        H beta
  have hEnvelope :
      Tendsto
        (fun n : ℕ => (rho ^ n * R) * (∫ X, |F X| ∂μ))
        atTop (𝓝 0) := by
    have hRight :=
      (hPow.mul_const R).mul_const (∫ X, |F X| ∂μ)
    simpa [mul_assoc] using hRight
  have hAbs :
      Tendsto
        (fun n : ℕ =>
          |realIntegralCovariance μ F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k G (n * L))|)
        atTop (𝓝 0) := by
    exact
      squeeze_zero'
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (Filter.Eventually.of_forall hBound)
        hEnvelope
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa [μ, L, Real.norm_eq_abs] using hAbs

end

end MathlibAnalytic
end MGAP4D
