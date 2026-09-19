import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScanPullbackResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceFiniteResolventClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

local instance physicalRestrictedRandomScanResolventClosureSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalRestrictedRandomScanResolventClosureSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalRestrictedRandomScanResolventClosureSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalRestrictedRandomScanResolventClosureSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalRestrictedRandomScanResolventClosureSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalRestrictedRandomScanResolventClosureSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A strict row bound on the physical-left pullback of the explicit tagged C5
kernel gives a uniform bound on the total finite restricted random-scan
resolvent profile.

This is the concrete specialization of the abstract restricted-target pullback
resolvent to the actual eligible embedding `fiber ↦ Sum.inl fiber`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile_total_le_resolvent
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta)
            (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber))
          target ≤ rowCoefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (M : ℕ) :
    (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
        H beta hbeta variation M (Sum.inl fiber)) ≤
      (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variation fiber) *
        (1 - rowCoefficient)⁻¹ := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
      H beta hbeta
  let targetEmbedding :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) :=
    fun fiber => Sum.inl fiber
  let initial :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
      H variation
  have hTarget : Function.Injective targetEmbedding := by
    intro a b hab
    exact Sum.inl.inj hab
  have hInitialNonneg : ∀ e, 0 ≤ initial e := by
    intro e
    cases e with
    | inl e =>
        simpa [initial,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
          hVariationNonneg e
    | inr e =>
        simp [initial,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
  have hRows :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback K targetEmbedding)
          target ≤ rowCoefficient := by
    simpa [K, targetEmbedding] using hRowSum
  have hRes :=
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_normalized_sum_eligibleTotal_le_resolvent
      K targetEmbedding hTarget hCard rowCoefficient hRowNonneg hRowLtOne
      hRows initial hInitialNonneg M
  have hProfileTotal :
      (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
          H beta hbeta variation M (Sum.inl fiber)) =
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (∑ m ∈ Finset.range M,
            ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                H beta hbeta variation m (Sum.inl fiber)) := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
  rw [hProfileTotal]
  simpa [
    K,
    targetEmbedding,
    initial,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
    hRes

/-- If the first observable's variation profile is uniformly bounded by
`variationFBound`, the physical finite resolvent pairing is uniformly bounded
by that envelope times the strict-row resolvent of the second observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile_weighted_le_resolvent
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta)
            (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber))
          target ≤ rowCoefficient)
    (variationF variationG : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationGNonneg : ∀ e, 0 ≤ variationG e)
    (variationFBound : ℝ)
    (hVariationFBoundNonneg : 0 ≤ variationFBound)
    (hVariationFBound : ∀ e, variationF e ≤ variationFBound)
    (M : ℕ) :
    (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
      variationF fiber *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
          H beta hbeta variationG M (Sum.inl fiber)) ≤
      variationFBound *
        ((∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationG fiber) *
          (1 - rowCoefficient)⁻¹) := by
  have hProfileNonneg :
      ∀ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta variationG M (Sum.inl fiber) := by
    intro fiber
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile_nonneg
        H beta hbeta variationG hVariationGNonneg M (Sum.inl fiber)
  have hPoint :
      ∀ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
              H beta hbeta variationG M (Sum.inl fiber) ≤
          variationFBound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
              H beta hbeta variationG M (Sum.inl fiber) := by
    intro fiber
    exact mul_le_mul_of_nonneg_right (hVariationFBound fiber) (hProfileNonneg fiber)
  have hTotal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile_total_le_resolvent
      H beta hbeta hCard rowCoefficient hRowNonneg hRowLtOne hRowSum
      variationG hVariationGNonneg M
  calc
    (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
      variationF fiber *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
          H beta hbeta variationG M (Sum.inl fiber)) ≤
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationFBound *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta variationG M (Sum.inl fiber) := by
      apply Finset.sum_le_sum
      intro fiber _h
      exact hPoint fiber
    _ =
      variationFBound *
        (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta variationG M (Sum.inl fiber)) := by
      rw [Finset.mul_sum]
    _ ≤
      variationFBound *
        ((∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationG fiber) *
          (1 - rowCoefficient)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hTotal hVariationFBoundNonneg

/-- The abstract finite-resolvent closure now becomes a concrete full covariance
bound once the physical-left pullback kernel has a strict row coefficient.

The only remaining contraction input is the explicit row estimate for the
eligible physical kernel; the complete-block ergodic remainder has already
been removed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_abs_le_eligibleRow_resolvent
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
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |G X - G Y| ≤ R)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ eligibleTarget : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta)
            (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber))
          eligibleTarget ≤ rowCoefficient)
    (variationFBound : ℝ)
    (hVariationFBoundNonneg : 0 ≤ variationFBound)
    (hVariationFBound : ∀ e, variationF e ≤ variationFBound) :
    |realIntegralCovariance
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂))
      F G| ≤
      variationFBound *
        ((∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationG fiber) *
          (1 - rowCoefficient)⁻¹) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_abs_le_of_uniform_completeBlock_finiteResolventProfile
      H N hN beta hbeta B hne hNoShare g₂ k F G
      hFStrong hGStrong hF hG variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG
      R
      (variationFBound *
        ((∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationG fiber) *
          (1 - rowCoefficient)⁻¹))
      hR hOsc
  intro n
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile_weighted_le_resolvent
      H beta hbeta hCard rowCoefficient hRowNonneg hRowLtOne hRowSum
      variationF variationG hVariationGNonneg
      variationFBound hVariationFBoundNonneg hVariationFBound
      (n *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length)

end

end MathlibAnalytic
end MGAP4D
