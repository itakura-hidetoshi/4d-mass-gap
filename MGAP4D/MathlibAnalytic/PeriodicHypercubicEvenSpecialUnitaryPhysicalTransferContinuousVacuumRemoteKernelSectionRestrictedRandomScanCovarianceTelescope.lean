import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanIterate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionRestrictedRandomScanCovarianceTelescopeKernelSectionProbabilityMeasure
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
    H N hN beta hbeta C

/-- Normalized finite restricted random-scan resolvent profile on the augmented
one-way tagged carrier.  Only physical left fibers are scanned, so the
normalization is by the number of physical spatial links rather than by the
cardinality of the full tagged sum type. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (M : Nat)
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) : Real :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : Real)⁻¹ *
    ∑ m ∈ Finset.range M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta variation m e

/-- The finite restricted random-scan resolvent profile is nonnegative for a
nonnegative initial physical variation profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile_nonneg
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (hVariationNonneg : forall e, 0 <= variation e)
    (M : Nat)
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 <=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
        H beta hbeta variation M e := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg fun m _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
        H beta hbeta variation hVariationNonneg m e

/-- Finite algebra identifying the time-sum of restricted random-scan diagonal
variation products with the dot product against the normalized restricted
finite resolvent profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScan_average_dot_variationIterates_eq_dot_finiteResolventProfile
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (a variation : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (M : Nat) :
    (Finset.range M).sum
        (fun m =>
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : Real)⁻¹ *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                  H beta hbeta variation m (Sum.inl e)) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        a e *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta variation M (Sum.inl e) := by
  classical
  let n : Real := Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  calc
    (Finset.range M).sum
        (fun m =>
          n⁻¹ *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                  H beta hbeta variation m (Sum.inl e)) =
      n⁻¹ *
        (Finset.range M).sum
          (fun m =>
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                  H beta hbeta variation m (Sum.inl e)) := by
        rw [← Finset.mul_sum]
    _ = n⁻¹ *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (Finset.range M).sum
            (fun m =>
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                  H beta hbeta variation m (Sum.inl e)) := by
        rw [Finset.sum_comm]
    _ = n⁻¹ *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          a e *
            (Finset.range M).sum
              (fun m =>
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                  H beta hbeta variation m (Sum.inl e)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.mul_sum]
    _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        a e *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta variation M (Sum.inl e) := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- Exact finite covariance telescope along the actual physical restricted
random-scan orbit.  This is pure finite algebra and makes no asymptotic or
decay claim. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_telescope
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (M : Nat) :
    realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        F G -
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k G M) =
      (Finset.range M).sum
        (fun m =>
          realIntegralCovariance
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
                H N hN beta hbeta
                (Function.update (Function.update B source k) target g2))
              F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g2 k G m) -
            realIntegralCovariance
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
                H N hN beta hbeta
                (Function.update (Function.update B source k) target g2))
              F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g2 k G (m + 1))) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      linarith

/-- The finite physical restricted random-scan covariance remainder is bounded
by the left variation of the first observable paired with the normalized
finite restricted tagged resolvent profile generated by the second observable.

This is finite-volume and finite in update count.  It does not assert that the
remainder vanishes, spatial covariance decay, or a continuum/Hamiltonian mass
gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_finiteResolventProfile
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hFStrong : StronglyMeasurable F)
    (hGStrong : StronglyMeasurable G)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)))
    (hG : MemLp G 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)))
    (variationF variationG : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (hVariationFNonneg : forall e, 0 <= variationF e)
    (hVariationGNonneg : forall e, 0 <= variationG e)
    (hVariationF :
      forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |F (Function.update C e u) - F (Function.update C e v)| <= variationF e)
    (hVariationG :
      forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |G (Function.update C e u) - G (Function.update C e v)| <= variationG e)
    (M : Nat) :
    |realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        F G -
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k G M)| <=
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta variationG M (Sum.inl fiber) := by
  classical
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hTel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_telescope
      H N hN beta hbeta B target source g2 k F G M
  change
    |realIntegralCovariance mu F G -
      realIntegralCovariance mu F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k G M)| <= _
  rw [hTel]
  calc
    |(Finset.range M).sum
        (fun m =>
          realIntegralCovariance mu F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g2 k G m) -
            realIntegralCovariance mu F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g2 k G (m + 1)))| <=
      (Finset.range M).sum
        (fun m =>
          |realIntegralCovariance mu F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g2 k G m) -
            realIntegralCovariance mu F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g2 k G (m + 1))|) := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ <=
      (Finset.range M).sum
        (fun m =>
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : Real)⁻¹ *
            ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
              variationF fiber *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                  H beta hbeta variationG m (Sum.inl fiber)) := by
      apply Finset.sum_le_sum
      intro m _
      let Gm : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k G m
      let variationGm : PeriodicHypercubicEvenSpatialSliceLink H -> Real :=
        fun e =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta variationG m (Sum.inl e)
      have hGmStrong : StronglyMeasurable Gm := by
        dsimp [Gm]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g2 k G hGStrong m
      have hGm :
          MemLp Gm 2 mu := by
        dsimp [Gm, mu]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScanExpectationIterate_memLp_two
            H N hN beta hbeta B hne hNoShare g2 k G hG m
      have hVariationGmNonneg : forall e, 0 <= variationGm e := by
        intro e
        dsimp [variationGm]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
            H beta hbeta variationG hVariationGNonneg m (Sum.inl e)
      have hVariationGm :
          forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
            |Gm (Function.update C e u) - Gm (Function.update C e v)| <=
              variationGm e := by
        intro e C u v
        simpa [Gm, variationGm] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le
            H N hN beta hbeta B target source g2 k G hGStrong variationG
            hVariationGNonneg hVariationG m e C u v
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_decrement_abs_le_average_variation_products
          H N hN beta hbeta B hne hNoShare k g2 F Gm
          hFStrong hGmStrong hF hGm variationF variationGm
          hVariationFNonneg hVariationGmNonneg hVariationF hVariationGm
      simpa [
        Gm,
        variationGm,
        mu,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ] using
        hStep
    _ =
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanFiniteResolventProfile
            H beta hbeta variationG M (Sum.inl fiber) := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScan_average_dot_variationIterates_eq_dot_finiteResolventProfile
          H beta hbeta variationF variationG M

end

end MathlibAnalytic
end MGAP4D
