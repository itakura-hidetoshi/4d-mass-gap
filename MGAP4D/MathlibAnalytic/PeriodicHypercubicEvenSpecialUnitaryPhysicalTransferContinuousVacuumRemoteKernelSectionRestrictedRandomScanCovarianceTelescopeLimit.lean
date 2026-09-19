import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceSubsequenceLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable section

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeLimitSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeLimitSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeLimitSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeLimitSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeLimitSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeLimitSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Along complete restricted random-scan blocks, the finite covariance
increment telescope converges to the full fixed-right covariance.

This closes the finite-update remainder on the subsequence
`M = n * length(allSpatialLinkSchedule H)` by combining the exact finite
covariance telescope with the Doeblin block-subsequence covariance remainder
limit.  No spatial covariance decay, coercivity, Poincare inequality, or mass
gap input is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_telescopeSum_mul_scheduleLength_tendsto_covariance
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
        (Finset.range
          (n *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length)).sum
          (fun m =>
            realIntegralCovariance
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
                  H N hN beta hbeta
                  (Function.update (Function.update B source k) target g₂))
                F
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                  H N hN beta hbeta B target source g₂ k G m) -
              realIntegralCovariance
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
                  H N hN beta hbeta
                  (Function.update (Function.update B source k) target g₂))
                F
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                  H N hN beta hbeta B target source g₂ k G (m + 1))))
      atTop
      (𝓝
        (realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          F G)) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  let L :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length
  have hRem :
      Tendsto
        (fun n : ℕ =>
          realIntegralCovariance μ F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k G (n * L)))
        atTop (𝓝 0) := by
    dsimp [μ, L]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_mul_scheduleLength_tendsto_zero
        H N hN beta hbeta B hne hNoShare g₂ k F G hGStrong hF hG R hR hOsc
  have hDiff :
      Tendsto
        (fun n : ℕ =>
          realIntegralCovariance μ F G -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (n * L)))
        atTop (𝓝 (realIntegralCovariance μ F G)) := by
    have h :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => realIntegralCovariance μ F G)
          atTop (𝓝 (realIntegralCovariance μ F G))).sub hRem
    simpa using h
  have hFunction :
      (fun n : ℕ =>
        (Finset.range (n * L)).sum
          (fun m =>
            realIntegralCovariance μ F
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                  H N hN beta hbeta B target source g₂ k G m) -
              realIntegralCovariance μ F
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                  H N hN beta hbeta B target source g₂ k G (m + 1)))) =
        (fun n : ℕ =>
          realIntegralCovariance μ F G -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (n * L))) := by
    funext n
    symm
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_telescope
        H N hN beta hbeta B target source g₂ k F G (n * L)
  change
    Tendsto
      (fun n : ℕ =>
        (Finset.range (n * L)).sum
          (fun m =>
            realIntegralCovariance μ F
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                  H N hN beta hbeta B target source g₂ k G m) -
              realIntegralCovariance μ F
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                  H N hN beta hbeta B target source g₂ k G (m + 1))))
      atTop (𝓝 (realIntegralCovariance μ F G))
  rw [hFunction]
  exact hDiff

end

end MathlibAnalytic
end MGAP4D
