import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedDistance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalSpatialCovarianceDecay
import Mathlib.Tactic

/-!
# Primary-plaquette seed-distance covariance decay

P3-A gives the exact distance from an arbitrary spatial link to the four-link
canonical primary-plaquette seed. PR #5199 gives actual posterior local-factor
covariance decay in the ordered source-to-target base-L1 distance.

For a source outside the radius-two seed neighbourhood, the P3-A geometry
supplies the exact distinctness and non-plaquette-local hypotheses required by
#5199 for every one of the four seed links. Since the seed distance is the
minimum of those four base-L1 distances, monotonicity of s^n for s >= 1 turns
the #5199 denominator into the intrinsic seed-distance denominator.

This is a pointwise covariance bridge. It does not yet identify the centered
source-coordinate L2 projection of the actual frozen orbit with a finite sum of
these covariances, and it does not estimate the retained output/half-density
drift.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every radius-two-exterior source link has canonical posterior local-factor
covariance decay measured directly by its distance to the primary-plaquette
seed. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeed_localFactorCovariance_abs_le_seedDistancePower
    (H : ℕ)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (k : Fin 4)
    (hFar : 2 < physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta /
        s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
  rcases
      physicalYangMillsSU2PrimaryPlaquetteSeedDistance_gt_two_remote
        H source hFar k with
    ⟨hSeedNe, hRemote⟩
  have hCov :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrap_localFactorCovariance_abs_le_baseL1Power
      H 2 specialUnitaryTwoWilsonRankPositive s hs beta hbeta hcut B
      (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) source sourceValue g
      hSeedNe.symm hRemote
  have hDistance :=
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance_le_covarianceDistance
      H source k
  have hPow :
      s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source ≤
        s ^
          periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H
              (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k)) :=
    pow_le_pow_right₀ hs hDistance
  have hPrefactor :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor_nonneg
      H 2 specialUnitaryTwoWilsonRankPositive s hs beta hbeta hcut
  have hsPos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  exact hCov.trans
    (div_le_div_of_nonneg_left hPrefactor
      (pow_pos hsPos _)
      hPow)

/-- Finset membership in the radius-two exterior gives the same pointwise
seed-distance covariance bound. -/
theorem physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovariance_abs_le_seedDistancePower
    (H : ℕ)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (k : Fin 4)
    (hFar : source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta /
        s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
  exact
    physicalYangMillsSU2PrimaryPlaquetteSeed_localFactorCovariance_abs_le_seedDistancePower
      H s hs beta hbeta hcut B source sourceValue g k
      ((physicalYangMillsSU2PrimaryPlaquette_mem_farLinks H 2 source).mp hFar)

end

end MathlibAnalytic
end MGAP4D
