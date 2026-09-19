import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceTelescopeLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

local instance remoteKernelSectionRestrictedRandomScanCovarianceFiniteResolventClosureSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionRestrictedRandomScanCovarianceFiniteResolventClosureSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance remoteKernelSectionRestrictedRandomScanCovarianceFiniteResolventClosureSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance remoteKernelSectionRestrictedRandomScanCovarianceFiniteResolventClosureSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance remoteKernelSectionRestrictedRandomScanCovarianceFiniteResolventClosureSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionRestrictedRandomScanCovarianceFiniteResolventClosureSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Uniform control of the complete-block finite restricted random-scan
resolvent profile closes to a bound on the full fixed-right covariance.

The temporal/ergodic remainder is discharged by the complete-block covariance
telescope limit.  Thus the remaining input is exactly a uniform bound on the
finite variation resolvent profile.  This theorem introduces no terminal
covariance-decay, physical contraction, Poincare/coercivity, or mass-gap
assumption. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_abs_le_of_uniform_completeBlock_finiteResolventProfile
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
    (hFStrong : StronglyMeasurable F)
    (hGStrong : StronglyMeasurable G)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)))
    (hG : MemLp G 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)))
    (variationF variationG : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationFNonneg : ∀ e, 0 ≤ variationF e)
    (hVariationGNonneg : ∀ e, 0 ≤ variationG e)
    (hVariationF :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C₀ e u) - F (Function.update C₀ e v)| ≤ variationF e)
    (hVariationG :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |G (Function.update C₀ e u) - G (Function.update C₀ e v)| ≤ variationG e)
    (R C : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |G X - G Y| ≤ R)
    (hFiniteResolventBound :
      ∀ n : ℕ,
        (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          variationF fiber *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
              H beta hbeta variationG
              (n *
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
                  H).length)
              (Sum.inl fiber)) ≤ C) :
    |realIntegralCovariance
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂))
      F G| ≤ C := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  let L :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length
  let S : ℕ → ℝ :=
    fun n =>
      (Finset.range (n * L)).sum
        (fun m =>
          realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G m) -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (m + 1)))
  have hTendsto :
      Tendsto S atTop (𝓝 (realIntegralCovariance μ F G)) := by
    dsimp [S, μ, L]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_telescopeSum_mul_scheduleLength_tendsto_covariance
        H N hN beta hbeta B hne hNoShare g₂ k F G hGStrong hF hG R hR hOsc
  have hAbsTendsto :
      Tendsto (fun n : ℕ => |S n|) atTop
        (𝓝 |realIntegralCovariance μ F G|) := by
    simpa using hTendsto.abs
  have hFinite : ∀ n : ℕ, |S n| ≤ C := by
    intro n
    have hPartial :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_finiteResolventProfile
        H N hN beta hbeta B hne hNoShare g₂ k F G
        hFStrong hGStrong hF hG variationF variationG
        hVariationFNonneg hVariationGNonneg hVariationF hVariationG (n * L)
    have hTel :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_telescope
        H N hN beta hbeta B target source g₂ k F G (n * L)
    change
      |realIntegralCovariance μ F G -
        realIntegralCovariance μ F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k G (n * L))| ≤
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          variationF fiber *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
              H beta hbeta variationG (n * L) (Sum.inl fiber) at hPartial
    change
      realIntegralCovariance μ F G -
        realIntegralCovariance μ F
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k G (n * L)) =
        S n at hTel
    have hProfileBound :
        (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          variationF fiber *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
              H beta hbeta variationG (n * L) (Sum.inl fiber)) ≤ C := by
      dsimp [L]
      exact hFiniteResolventBound n
    calc
      |S n| =
          |realIntegralCovariance μ F G -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (n * L))| := by
          rw [hTel]
      _ ≤
          ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            variationF fiber *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
                H beta hbeta variationG (n * L) (Sum.inl fiber) := hPartial
      _ ≤ C := hProfileBound
  change |realIntegralCovariance μ F G| ≤ C
  exact le_of_tendsto' hAbsTendsto hFinite

end

end MathlibAnalytic
end MGAP4D
