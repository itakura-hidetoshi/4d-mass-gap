import MGAP4D.MathlibAnalytic.RealIntegralCovarianceFiniteLinearity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkCovarianceLocalVariation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRestrictedRandomScanTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance remoteKernelSectionRestrictedRandomScanCovarianceDirichletSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionRestrictedRandomScanCovarianceDirichletSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionRestrictedRandomScanCovarianceDirichletKernelSectionProbabilityMeasure
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

/-- One actual physical restricted random-scan step preserves L2 under the
fixed remote kernel-section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScanExpectation_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    MemLp
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
          H N hN beta hbeta B target source g2 k A F)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  let P :
      PeriodicHypercubicEvenSpatialSliceLink H ->
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
    fun fiber A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g2 [fiber] k A F
  have hP :
      forall fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        MemLp (P fiber) 2 mu := by
    intro fiber
    dsimp [P, mu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleExpectation_memLp_two
        H N hN beta hbeta B hne hNoShare [fiber] k g2 F hF
  have hSum :
      MemLp
        (fun A => ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, P fiber A)
        2 mu := by
    classical
    exact
      memLp_finset_sum Finset.univ
        (fun fiber _ => hP fiber)
  have hScaled :=
    hSum.const_mul
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : Real)⁻¹
  simpa [
    mu, P,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation] using
    hScaled

/-- Exact covariance Dirichlet identity for one actual physical restricted
random-scan step.  The covariance decrement is the uniform average of the
actual one-link fluctuation covariance pairings.  No commutation of distinct
one-link projections is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_decrement_eq_average_oneLinkFluctuation_pairings
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)))
    (hG : MemLp G 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
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
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
            H N hN beta hbeta B target source g2 k A G) =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : Real)⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          realIntegralCovariance
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g2))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 F)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 G) := by
  classical
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  let n : Real := Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let P :
      PeriodicHypercubicEvenSpatialSliceLink H ->
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
    fun fiber A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g2 [fiber] k A G
  have hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hnPos : 0 < n := by
    dsimp [n]
    exact_mod_cast hCard
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  have hP :
      forall fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        MemLp (P fiber) 2 mu := by
    intro fiber
    dsimp [P, mu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleExpectation_memLp_two
        H N hN beta hbeta B hne hNoShare [fiber] k g2 G hG
  have hSum :
      MemLp
        (fun A => ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, P fiber A)
        2 mu := by
    exact
      memLp_finset_sum Finset.univ
        (fun fiber _ => hP fiber)
  have hScale :=
    realIntegralCovariance_const_mul_right_of_memLp_two
      mu n⁻¹ F
      (fun A => ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, P fiber A)
      hF hSum
  have hSumCov :=
    realIntegralCovariance_fintype_sum_right_of_memLp_two
      mu F P hF hP
  have hOneLink :
      forall fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        realIntegralCovariance mu F G -
            realIntegralCovariance mu F (P fiber) =
          realIntegralCovariance mu
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 F)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 G) := by
    intro fiber
    have hDirichlet :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLink_realIntegralCovariance_sub_projection_eq_fluctuation_pairing_of_memLp_two
        H N hN beta hbeta B hne hNoShare fiber k g2 F G hF hG
    have hBridgeRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_schedule_eq_schedule_cons
        H N hN beta hbeta B target source fiber [] k g2 G
    have hBridge :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 G =
          P fiber := by
      simpa only [
        P,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_nil] using
        hBridgeRaw
    change
      realIntegralCovariance mu F G -
          realIntegralCovariance mu F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
              H N hN beta hbeta B target source fiber k g2 G) =
        realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 F)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 G) at hDirichlet
    rw [hBridge] at hDirichlet
    exact hDirichlet
  change
    realIntegralCovariance mu F G -
      realIntegralCovariance mu F
        (fun A => n⁻¹ * ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, P fiber A) =
      n⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          realIntegralCovariance mu
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 F)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 G)
  rw [hScale, hSumCov]
  have hConst :
      (∑ _fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          realIntegralCovariance mu F G) =
        n * realIntegralCovariance mu F G := by
    simp [n, nsmul_eq_mul]
  calc
    realIntegralCovariance mu F G -
        n⁻¹ *
          ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            realIntegralCovariance mu F (P fiber) =
      n⁻¹ *
        (n * realIntegralCovariance mu F G -
          ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
            realIntegralCovariance mu F (P fiber)) := by
      field_simp [hnNe]
    _ = n⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          (realIntegralCovariance mu F G -
            realIntegralCovariance mu F (P fiber)) := by
      rw [Finset.sum_sub_distrib, hConst]
    _ = n⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          realIntegralCovariance mu
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 F)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
              H N hN beta hbeta B target source fiber k g2 G) := by
      congr 1
      apply Finset.sum_congr rfl
      intro fiber _
      exact hOneLink fiber

/-- The one-step actual restricted random-scan covariance decrement is bounded
by the uniform average of the diagonal products of the two physical-link
variation profiles.  This remains a finite-volume one-step estimate and does
not assert spatial covariance decay. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_decrement_abs_le_average_variation_products
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
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
        |G (Function.update C e u) - G (Function.update C e v)| <= variationG e) :
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
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
            H N hN beta hbeta B target source g2 k A G)| <=
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : Real)⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          variationF fiber * variationG fiber := by
  classical
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  let n : Real := Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hnPos : 0 < n := by
    dsimp [n]
    exact_mod_cast hCard
  have hnInvNonneg : 0 <= n⁻¹ :=
    inv_nonneg.mpr hnPos.le
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_decrement_eq_average_oneLinkFluctuation_pairings
      H N hN beta hbeta B hne hNoShare k g2 F G hF hG]
  change
    |n⁻¹ *
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 F)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 G)| <=
      n⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          variationF fiber * variationG fiber
  rw [abs_mul, abs_of_nonneg hnInvNonneg]
  apply mul_le_mul_of_nonneg_left _ hnInvNonneg
  calc
    |∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 F)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 G)| <=
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        |realIntegralCovariance mu
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 F)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta B target source fiber k g2 G)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber * variationG fiber := by
      apply Finset.sum_le_sum
      intro fiber _
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuations_realIntegralCovariance_abs_le_variation_mul_variation
          H N hN beta hbeta B hne hNoShare fiber k g2 F G
          hFStrong hGStrong hF hG variationF variationG
          hVariationFNonneg hVariationGNonneg hVariationF hVariationG

end

end MathlibAnalytic
end MGAP4D
