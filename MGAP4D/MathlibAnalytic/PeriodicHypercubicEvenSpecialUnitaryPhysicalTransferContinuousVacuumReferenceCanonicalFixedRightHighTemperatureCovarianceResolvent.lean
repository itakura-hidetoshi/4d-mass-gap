import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRandomScanContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceDirichlet
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceSubsequenceLimit
import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelStrictFiniteResponseAsymptotic
import Mathlib.Tactic

/-!
# Canonical high-temperature covariance resolvent

The canonical high-temperature physical influence theorem and its random-scan
bridge now give an ordinary column coefficient

  q = CanonicalFixedRightHalfBarrierPinFreeCoefficient 1 beta < 1

for the actual canonical pin-free physical influence kernel.

This file feeds that strict coefficient into the existing finite random-scan
covariance telescope.  The normalized finite resolvent carries a factor
|links|^-1, while the reciprocal random-scan gap is exactly
|links|^-1 * (1 - q).  The repository theorem

  inv_card_mul_finiteRealGeometricSeries_le_one_sub_inv

therefore cancels the finite-volume cardinality and yields the uniform
resolvent denominator (1 - q)^-1.

The final theorem combines this finite resolvent estimate with the already
proved fixed-volume complete-block covariance remainder limit.  It gives a
volume-independent Dobrushin-type covariance bound in terms of the total
variation profile of the first observable and a uniform variation bound for
the second observable.

This is not yet spatial covariance clustering, a Poincare/coercivity
inequality, a Hamiltonian spectral gap, or a continuum construction.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

local instance canonicalHighTemperatureCovarianceResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalHighTemperatureCovarianceResolventSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalHighTemperatureCovarianceResolventSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalHighTemperatureCovarianceResolventSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalHighTemperatureCovarianceResolventSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalHighTemperatureCovarianceResolventSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical pin-free response-controlled random-scan orbit obeys the
common high-temperature reciprocal rate at every finite update depth. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_le_rate_pow_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (n : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)
        variation n source ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            1 beta) ^ n *
        bound := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_eq_kernel]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_randomScanVariationIterate_le_rate_pow_mul
      H N hN beta hbeta hcut variation hVariationNonneg
      bound hBoundNonneg hVariationBound n source

/-- Normalized finite resolvent profile of the canonical pin-free physical
random-scan variation orbit. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (M : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
    ∑ m ∈ Finset.range M,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)
        variation m e

/-- The canonical finite resolvent profile is nonnegative for a nonnegative
initial variation profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (M : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M e := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg fun m _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_nonneg
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)
        variation hVariationNonneg m e

/-- Finite algebra: the time-sum of covariance variation pairings is exactly
the dot product against the normalized canonical finite resolvent profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScan_average_dot_variationIterates_eq_dot_finiteResolventProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (a variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (M : ℕ) :
    (Finset.range M).sum
        (fun m =>
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
                  H beta hbeta
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                    H N hN beta hbeta)
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                    H N hN beta hbeta)
                  variation m e) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        a e *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
            H N hN beta hbeta variation M e := by
  classical
  let n : ℝ := Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  calc
    (Finset.range M).sum
        (fun m =>
          n⁻¹ *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
                  H beta hbeta
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                    H N hN beta hbeta)
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                    H N hN beta hbeta)
                  variation m e) =
      n⁻¹ *
        (Finset.range M).sum
          (fun m =>
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
                  H beta hbeta
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                    H N hN beta hbeta)
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                    H N hN beta hbeta)
                  variation m e) := by
        rw [← Finset.mul_sum]
    _ = n⁻¹ *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (Finset.range M).sum
            (fun m =>
              a e *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
                  H beta hbeta
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                    H N hN beta hbeta)
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                    H N hN beta hbeta)
                  variation m e) := by
        rw [Finset.sum_comm]
    _ = n⁻¹ *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          a e *
            (Finset.range M).sum
              (fun m =>
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
                  H beta hbeta
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                    H N hN beta hbeta)
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                    H N hN beta hbeta)
                  variation m e) := by
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.mul_sum]
    _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        a e *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
            H N hN beta hbeta variation M e := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- The normalized canonical finite resolvent is uniformly bounded by the
volume-independent Dobrushin denominator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_resolvent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (M : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M e ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          1 beta)⁻¹ *
        bound := by
  classical
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      1 beta
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H) q
  have hCard :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hQ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      1 beta hbeta hcut
  have hPrefix :
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          finiteRealGeometricSeries rate M ≤
        (1 - q)⁻¹ := by
    simpa [q, rate] using
      inv_card_mul_finiteRealGeometricSeries_le_one_sub_inv
        (ι := PeriodicHypercubicEvenSpatialSliceLink H)
        hCard hQ.1 hQ.2 M
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
  calc
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ m ∈ Finset.range M,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)
            variation m e ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ m ∈ Finset.range M, rate ^ m * bound := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro m _hm
            simpa [q, rate] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_le_rate_pow_mul
                H N hN beta hbeta hcut variation hVariationNonneg
                bound hBoundNonneg hVariationBound m e
          · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    _ =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        finiteRealGeometricSeries rate M) * bound := by
          rw [finiteRealGeometricSeries]
          rw [← Finset.sum_mul]
          ring
    _ ≤ (1 - q)⁻¹ * bound :=
      mul_le_mul_of_nonneg_right hPrefix hBoundNonneg
    _ =
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          1 beta)⁻¹ * bound := by
      rfl

/-- The actual finite physical random-scan covariance telescope is controlled
by the canonical finite resolvent profile, with no tagged-carrier majorant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureResolvent
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
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variationF e)
    (hVariationG :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |G (Function.update C e u) - G (Function.update C e v)| ≤ variationG e)
    (M : ℕ) :
    |realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        F G -
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k G M)| ≤
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
            H N hN beta hbeta variationG M fiber := by
  classical
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  have hTel :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_telescope
      H N hN beta hbeta B target source g₂ k F G M
  change
    |realIntegralCovariance μ F G -
      realIntegralCovariance μ F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k G M)| ≤ _
  rw [hTel]
  calc
    |(Finset.range M).sum
        (fun m =>
          realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G m) -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (m + 1)))| ≤
      (Finset.range M).sum
        (fun m =>
          |realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G m) -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (m + 1))|) := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤
      (Finset.range M).sum
        (fun m =>
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
            ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
              variationF fiber *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
                  H beta hbeta
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                    H N hN beta hbeta)
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                    H N hN beta hbeta)
                  variationG m fiber) := by
      apply Finset.sum_le_sum
      intro m _hm
      let Gm : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k G m
      let variationGm : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
        fun e =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)
            variationG m e
      have hGmStrong : StronglyMeasurable Gm := by
        dsimp [Gm]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g₂ k G hGStrong m
      have hGm :
          MemLp Gm 2 μ := by
        dsimp [Gm, μ]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScanExpectationIterate_memLp_two
            H N hN beta hbeta B hne hNoShare g₂ k G hG m
      have hVariationGmNonneg : ∀ e, 0 ≤ variationGm e := by
        intro e
        dsimp [variationGm]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_nonneg
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)
            variationG hVariationGNonneg m e
      have hVariationGm :
          ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
            |Gm (Function.update C e u) - Gm (Function.update C e v)| ≤
              variationGm e := by
        intro e C u v
        dsimp [Gm, variationGm]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_pinFreeResponseControlled
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_uniformBound
              H N hN beta hbeta)
            B target source g₂ k G hGStrong variationG hVariationGNonneg hVariationG
            m e C u v
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_decrement_abs_le_average_variation_products
          H N hN beta hbeta B hne hNoShare k g₂ F Gm
          hFStrong hGmStrong hF hGm variationF variationGm
          hVariationFNonneg hVariationGmNonneg hVariationF hVariationGm
      simpa [
        Gm,
        variationGm,
        μ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ] using
        hStep
    _ =
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
            H N hN beta hbeta variationG M fiber := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScan_average_dot_variationIterates_eq_dot_finiteResolventProfile
          H N hN beta hbeta variationF variationG M

/-- Uniform finite covariance-telescope bound.  The finite-volume cardinality
has disappeared from the resolvent denominator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureUniform
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
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
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variationF e)
    (hVariationG :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |G (Function.update C e u) - G (Function.update C e v)| ≤ variationG e)
    (boundG : ℝ)
    (hBoundGNonneg : 0 ≤ boundG)
    (hVariationGBound : ∀ e, variationG e ≤ boundG)
    (M : ℕ) :
    |realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        F G -
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k G M)| ≤
      (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationF fiber) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            1 beta)⁻¹ * boundG) := by
  have hPartial :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureResolvent
      H N hN beta hbeta B hne hNoShare g₂ k F G
      hFStrong hGStrong hF hG variationF variationG
      hVariationFNonneg hVariationGNonneg hVariationF hVariationG M
  calc
    |realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        F G -
      realIntegralCovariance
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        F
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k G M)| ≤
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
            H N hN beta hbeta variationG M fiber := hPartial
    _ ≤
      ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        variationF fiber *
          ((1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              1 beta)⁻¹ * boundG) := by
        apply Finset.sum_le_sum
        intro fiber _hf
        exact
          mul_le_mul_of_nonneg_left
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_resolvent
              H N hN beta hbeta hcut variationG hVariationGNonneg
              boundG hBoundGNonneg hVariationGBound M fiber)
            (hVariationFNonneg fiber)
    _ =
      (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationF fiber) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            1 beta)⁻¹ * boundG) := by
      rw [Finset.sum_mul]

/-- Full fixed-right remote kernel-section covariance bound obtained by sending
the complete-block random-scan remainder to zero.  The resulting resolvent
constant is independent of the number of spatial links. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSection_realIntegralCovariance_abs_le_canonicalHighTemperatureResolvent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          1)
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
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variationF e)
    (hVariationG :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |G (Function.update C e u) - G (Function.update C e v)| ≤ variationG e)
    (boundG : ℝ)
    (hBoundGNonneg : 0 ≤ boundG)
    (hVariationGBound : ∀ e, variationG e ≤ boundG)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |G X - G Y| ≤ R) :
    |realIntegralCovariance
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂))
      F G| ≤
      (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationF fiber) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            1 beta)⁻¹ * boundG) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  let L :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length
  let C :=
    (∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, variationF fiber) *
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          1 beta)⁻¹ * boundG)
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
        H N hN beta hbeta B hne hNoShare g₂ k F G
        hGStrong hF hG R hR hOsc
  have hDiff :
      Tendsto
        (fun n : ℕ =>
          realIntegralCovariance μ F G -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (n * L)))
        atTop (𝓝 (realIntegralCovariance μ F G)) := by
    have hConst :
        Tendsto (fun _ : ℕ => realIntegralCovariance μ F G)
          atTop (𝓝 (realIntegralCovariance μ F G)) :=
      tendsto_const_nhds
    simpa using hConst.sub hRem
  have hAbs :
      Tendsto
        (fun n : ℕ =>
          |realIntegralCovariance μ F G -
            realIntegralCovariance μ F
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
                H N hN beta hbeta B target source g₂ k G (n * L))|)
        atTop (𝓝 |realIntegralCovariance μ F G|) := by
    simpa using hDiff.abs
  have hFinite :
      ∀ n : ℕ,
        |realIntegralCovariance μ F G -
          realIntegralCovariance μ F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
              H N hN beta hbeta B target source g₂ k G (n * L))| ≤ C := by
    intro n
    dsimp [C, L, μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScan_realIntegralCovariance_partial_telescope_abs_le_canonicalHighTemperatureUniform
        H N hN beta hbeta hcut B hne hNoShare g₂ k F G
        hFStrong hGStrong hF hG variationF variationG
        hVariationFNonneg hVariationGNonneg hVariationF hVariationG
        boundG hBoundGNonneg hVariationGBound
        (n *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length)
  change |realIntegralCovariance μ F G| ≤ C
  exact le_of_tendsto' hAbs hFinite

end

end MGAP4D.MathlibAnalytic
