import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkCovarianceLocalVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionDeterministicScheduleCovarianceVariationSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionDeterministicScheduleCovarianceVariationSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionDeterministicScheduleCovarianceVariationKernelSectionProbabilityMeasure
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

/-- Recursive local-variation majorant for the exact deterministic-schedule
covariance telescope.  At a head fiber, the right observable has already been
transported through the tail schedule, so its retained local variation is the
exact tagged deterministic-schedule variation of that tail. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (variationF variationG : PeriodicHypercubicEvenSpatialSliceLink H -> Real) :
    List (PeriodicHypercubicEvenSpatialSliceLink H) -> Real
  | [] => 0
  | fiber :: fibers =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant
          H beta hbeta variationF variationG fibers +
        variationF fiber *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
            H beta hbeta variationG fibers (Sum.inl fiber)

/-- The deterministic-schedule covariance variation majorant is nonnegative
whenever the two declared variation profiles are nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant_nonneg
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (variationF variationG : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (hVariationFNonneg : forall e, 0 <= variationF e)
    (hVariationGNonneg : forall e, 0 <= variationG e) :
    forall fibers : List (PeriodicHypercubicEvenSpatialSliceLink H),
      0 <=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant
          H beta hbeta variationF variationG fibers := by
  intro fibers
  induction fibers with
  | nil =>
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant]
  | cons fiber fibers ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant]
      exact add_nonneg ih
        (mul_nonneg
          (hVariationFNonneg fiber)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_nonneg
            H beta hbeta variationG hVariationGNonneg fibers (Sum.inl fiber)))

/-- The absolute exact covariance-loss sum along a finite ordered literal-C5
schedule is bounded by the recursive product of the left local variation and
the tail-transported right tagged variation at each updated fiber.

This retains the full ordered tagged profile.  It does not collapse the right
profile to a total variation sum and does not assert spatial decay. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum_abs_le_variationMajorant
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
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
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
        H N hN beta hbeta B target source k g2 F G fibers| <=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant
        H beta hbeta variationF variationG fibers := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  induction fibers with
  | nil =>
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant]
  | cons fiber fibers ih =>
      let GTail : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
        fun A =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g2 fibers k A G
      let tailVariation : PeriodicHypercubicEvenSpatialSliceLink H -> Real :=
        fun e =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
            H beta hbeta variationG fibers (Sum.inl e)
      have hGTailStrong : StronglyMeasurable GTail := by
        dsimp [GTail]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_stronglyMeasurable
            H N hN beta hbeta B target source g2 k fibers G hGStrong
      have hGTail :
          MemLp GTail 2 mu := by
        dsimp [GTail, mu]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleExpectation_memLp_two
            H N hN beta hbeta B hne hNoShare fibers k g2 G hG
      have hTailVariationNonneg : forall e, 0 <= tailVariation e := by
        intro e
        dsimp [tailVariation]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_nonneg
            H beta hbeta variationG hVariationGNonneg fibers (Sum.inl e)
      have hGTailVariation :
          forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
            |GTail (Function.update C e u) - GTail (Function.update C e v)| <=
              tailVariation e := by
        intro e C u v
        simpa [GTail, tailVariation] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_fiberVariation_le
            H N hN beta hbeta B target source g2 k G hGStrong variationG
            hVariationGNonneg hVariationG fibers e C u v
      have hLocal :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuations_realIntegralCovariance_abs_le_variation_mul_variation
          H N hN beta hbeta B hne hNoShare fiber k g2 F GTail
          hFStrong hGTailStrong hF hGTail variationF tailVariation
          hVariationFNonneg hTailVariationNonneg hVariationF hGTailVariation
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant]
      have hTri :
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
                H N hN beta hbeta B target source k g2 F G fibers +
              realIntegralCovariance mu
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                  H N hN beta hbeta B target source fiber k g2 F)
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                  H N hN beta hbeta B target source fiber k g2 GTail)| <=
            |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
                H N hN beta hbeta B target source k g2 F G fibers| +
              |realIntegralCovariance mu
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                  H N hN beta hbeta B target source fiber k g2 F)
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                  H N hN beta hbeta B target source fiber k g2 GTail)| := by
        simpa [Real.norm_eq_abs] using
          norm_add_le
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
              H N hN beta hbeta B target source k g2 F G fibers)
            (realIntegralCovariance mu
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 F)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 GTail))
      calc
        |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
              H N hN beta hbeta B target source k g2 F G fibers +
            realIntegralCovariance mu
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 F)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 GTail)| <=
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum
              H N hN beta hbeta B target source k g2 F G fibers| +
            |realIntegralCovariance mu
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 F)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta B target source fiber k g2 GTail)| := hTri
        _ <=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant
              H beta hbeta variationF variationG fibers +
            variationF fiber *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
                H beta hbeta variationG fibers (Sum.inl fiber) := by
          apply add_le_add ih
          simpa [GTail, tailVariation, mu] using hLocal

/-- Absolute covariance loss through an arbitrary finite ordered literal-C5
schedule is bounded by the retained tagged local-variation majorant.  This is
the quantitative bridge from the exact L2 covariance telescope to the existing
deterministic tagged variation propagation layer. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicSchedule_realIntegralCovariance_sub_schedule_abs_le_variationMajorant
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
            H N hN beta hbeta B target source g2 fibers k A G)| <=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceVariationMajorant
        H beta hbeta variationF variationG fibers := by
  have hTelescope :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicSchedule_realIntegralCovariance_telescope_of_memLp_two
      H N hN beta hbeta B hne hNoShare fibers k g2 F G hF hG
  rw [hTelescope]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionDeterministicScheduleCovarianceDirichletSum_abs_le_variationMajorant
      H N hN beta hbeta B hne hNoShare fibers k g2 F G
      hFStrong hGStrong hF hG variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG

end

end MathlibAnalytic
end MGAP4D
