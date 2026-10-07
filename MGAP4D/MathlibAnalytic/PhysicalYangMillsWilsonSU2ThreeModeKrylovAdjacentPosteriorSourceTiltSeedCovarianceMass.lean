import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSourceTiltSeedCovarianceDecay
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceMass
import Mathlib.Tactic

/-!
# Volume-independent source-only tilt covariance mass from primary-seed distance

PR #5235 transfers the primary-seed posterior covariance decay from the full
right-target local factor to the literal source-only right-link tilt used by the
signed joint response.  PR #5230 supplies the volume-independent polynomial
seed shells and their completed geometric mass.

This file composes those two results.  For every s > 1, the sum of absolute
posterior covariances between a fixed primary seed local factor and all
radius-two-exterior source-only tilts is bounded by one H-independent completed
seed-shell mass with prefactor

  exp(6 * beta) * covariancePrefactor(s, beta).

No source-coordinate L2 norm is identified with covariance here.  In
particular this theorem does not identify posterior covariance with the actual
frozen source-centered coordinate, does not remove the retained output drift,
and does not change any pair-Haar/posterior carrier distinction.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance p3PrimarySeedSourceTiltCovarianceMassSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For s > 1, the actual posterior absolute covariance mass between any fixed
primary seed link and all radius-two-exterior literal source-only tilts is
bounded by an H-independent completed seed-shell mass. -/
theorem physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_sourceRightLinkTiltCovarianceMass_le
    (H : ℕ)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (sourceValue :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (k : Fin 4) :
    (∑ source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2,
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g)
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
            H 2 beta B source (sourceValue source))|) ≤
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass
        (Real.exp (6 * beta) *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta)
        s⁻¹ := by
  classical
  have hsWeak : 1 ≤ s := hs.le
  have hsPos : 0 < s := lt_trans zero_lt_one hs
  have hInvNonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hsPos.le
  have hInvLtOne : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have hPrefactor :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor_nonneg
      H 2 specialUnitaryTwoWilsonRankPositive s hsWeak beta hbeta hcut
  have hC :
      0 ≤
        Real.exp (6 * beta) *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta :=
    mul_nonneg (Real.exp_pos _).le hPrefactor
  have hPointwise :
      (∑ source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2,
        |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
              H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g)
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
              H 2 beta B source (sourceValue source))|) ≤
        ∑ source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2,
          (Real.exp (6 * beta) *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
              s beta) *
            (s⁻¹) ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
    apply Finset.sum_le_sum
    intro source hSource
    have hCov :=
      physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_sourceRightLinkTiltCovariance_abs_le_seedDistancePower
        H s hsWeak beta hbeta hcut B source (sourceValue source) g k hSource
    simpa [div_eq_mul_inv, inv_pow, mul_assoc] using hCov
  have hFarToAll :
      (∑ source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2,
          (Real.exp (6 * beta) *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
              s beta) *
            (s⁻¹) ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) ≤
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (Real.exp (6 * beta) *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
              s beta) *
            (s⁻¹) ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2))
        (fun source _hUniv _hNotFar =>
          mul_nonneg hC
            (pow_nonneg hInvNonneg
              (physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source)))
  exact hPointwise.trans (hFarToAll.trans
    (physicalYangMillsSU2PrimaryPlaquetteSeedDistance_sum_geometric_le_mass
      H
      (Real.exp (6 * beta) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta)
      s⁻¹ hC hInvNonneg hInvLtOne))

end

end MathlibAnalytic
end MGAP4D
