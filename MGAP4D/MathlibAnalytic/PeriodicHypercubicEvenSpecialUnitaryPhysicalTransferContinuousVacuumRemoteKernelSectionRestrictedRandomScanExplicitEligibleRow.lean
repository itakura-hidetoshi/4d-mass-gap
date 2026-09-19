import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanEligibleRowResolventClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance physicalRestrictedRandomScanExplicitRowSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalRestrictedRandomScanExplicitRowSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalRestrictedRandomScanExplicitRowSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalRestrictedRandomScanExplicitRowSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalRestrictedRandomScanExplicitRowSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalRestrictedRandomScanExplicitRowSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The eligible physical-left pullback of the explicit tagged C5 kernel has
an exact constant row sum: every off-diagonal left-left entry is the same
off-fiber influence coefficient and the diagonal entry vanishes. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedEligiblePullback_rowSum_eq
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRowSum
        (finiteInfluenceKernelRestrictedTargetPullback
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
            H beta hbeta)
          (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber))
        target =
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
      H beta hbeta
  let s : Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Finset.univ.erase target
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
      beta
  have hDiag :
      K.influence (Sum.inl target) (Sum.inl target) = 0 := by
    exact K.influence_diagonal_zero (Sum.inl target)
  have hErase :
      (∑ source ∈ s, K.influence (Sum.inl target) (Sum.inl source)) =
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback K
            (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber))
          target := by
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (f := fun source => K.influence (Sum.inl target) (Sum.inl source))
      (Finset.mem_univ target)
    change
      (∑ source ∈ s, K.influence (Sum.inl target) (Sum.inl source)) +
          K.influence (Sum.inl target) (Sum.inl target) =
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence (Sum.inl target) (Sum.inl source) at h
    rw [hDiag, add_zero] at h
    simpa [finiteInfluenceKernelRowSum,
      finiteInfluenceKernelRestrictedTargetPullback] using h
  have hOff :
      (∑ source ∈ s, K.influence (Sum.inl target) (Sum.inl source)) =
        ∑ source ∈ s, c := by
    apply Finset.sum_congr rfl
    intro source hsource
    have hne : source ≠ target := Finset.ne_of_mem_erase hsource
    have htarget : target ≠ source := Ne.symm hne
    simpa [K, c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_left_of_ne
        H beta hbeta target source htarget
  have hCardNat :
      s.card =
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 := by
    simpa [s] using Finset.card_erase_of_mem (Finset.mem_univ target)
  calc
    finiteInfluenceKernelRowSum
        (finiteInfluenceKernelRestrictedTargetPullback
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
            H beta hbeta)
          (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber))
        target =
      ∑ source ∈ s, K.influence (Sum.inl target) (Sum.inl source) := by
        simpa [K] using hErase.symm
    _ = ∑ source ∈ s, c := hOff
    _ = (s.card : ℝ) * c := by
      simp
    _ =
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) := by
      rw [hCardNat]
      rfl

/-- The exact eligible row coefficient is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedEligiblePullback_rowCoefficient_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
      beta hbeta)

/-- Under the explicit finite-volume strict-row criterion, the full fixed-right
covariance satisfies the physical restricted-random-scan resolvent bound.

The criterion is deliberately stated at fixed volume.  No claim of uniformity
in `H` is made here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_abs_le_explicitEligibleRow_resolvent
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
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
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
          (1 -
            (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                beta))⁻¹) := by
  let rowCoefficient : ℝ :=
    (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta)
  have hRowNonneg : 0 ≤ rowCoefficient := by
    dsimp [rowCoefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedEligiblePullback_rowCoefficient_nonneg
        H beta hbeta
  have hRowSum :
      ∀ eligibleTarget : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta)
            (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber))
          eligibleTarget ≤ rowCoefficient := by
    intro eligibleTarget
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedEligiblePullback_rowSum_eq
        H beta hbeta eligibleTarget]
  simpa [rowCoefficient] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_abs_le_eligibleRow_resolvent
      H N hN beta hbeta B hne hNoShare g₂ k F G
      hFStrong hGStrong hF hG variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG
      R hR hOsc hCard rowCoefficient hRowNonneg hEligibleRowLtOne hRowSum
      variationFBound hVariationFBoundNonneg hVariationFBound

end

end MathlibAnalytic
end MGAP4D
