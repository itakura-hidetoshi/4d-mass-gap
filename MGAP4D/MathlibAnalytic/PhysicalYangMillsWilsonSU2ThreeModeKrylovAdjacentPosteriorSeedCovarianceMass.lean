import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedPolynomialShell
import MGAP4D.MathlibAnalytic.FiniteDistanceShellGeometricSum
import Mathlib.Tactic

/-!
# Volume-independent total covariance mass from primary-seed distance

PR #5228 gives pointwise decay of the actual posterior covariance between each
of the four primary-plaquette seed local factors and every radius-two-exterior
source link. PR #5229 gives a volume-independent polynomial bound for every
exact shell of the intrinsic four-link seed distance, together with summability
of that shell majorant against any geometric profile.

This file composes those two facts.

First, for any nonnegative prefactor C and 0 <= q < 1, the full finite-volume
sum
  sum_source C * q^(seedDistance source)
is bounded by one H-independent completed shell mass.

Second, taking q = s^(-1), s > 1, and C equal to the existing canonical
posterior covariance prefactor gives an H-independent bound for the sum of
absolute seed/local-factor covariances over the entire radius-two exterior.

This still does NOT identify the actual frozen source-coordinate conditional
projection norm with that covariance mass, and it does NOT estimate or discard
the retained output/half-density drift.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance p3PrimarySeedCovarianceMassSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Completed H-independent shell majorant for the primary-seed distance. -/
def physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass
    (C q : ℝ) : ℝ :=
  ∑' r : ℕ,
    physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant r *
      (C * q ^ r)

/-- The completed seed-distance mass is well-defined whenever 0 <= q < 1. -/
theorem summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass
    (C q : ℝ)
    (hqNonneg : 0 ≤ q)
    (hqLtOne : q < 1) :
    Summable (fun r : ℕ =>
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant r *
        (C * q ^ r)) :=
  summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_mul_geometric
    C q hqNonneg hqLtOne

/-- Any finite-volume geometric profile in the intrinsic primary-seed distance
is bounded by the completed H-independent polynomial-shell mass. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeedDistance_sum_geometric_le_mass
    (H : ℕ)
    (C q : ℝ)
    (hC : 0 ≤ C)
    (hqNonneg : 0 ≤ q)
    (hqLtOne : q < 1) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      C * q ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) ≤
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass C q := by
  classical
  let distance : PeriodicHypercubicEvenSpatialSliceLink H → ℕ :=
    physicalYangMillsSU2PrimaryPlaquetteSeedDistance H
  let cutoff : ℕ :=
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H, distance source) + 1
  have hDistance :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        distance source < cutoff := by
    intro source
    have hLe :
        distance source ≤
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H, distance target := by
      exact
        Finset.single_le_sum
          (fun target _hTarget => Nat.zero_le (distance target))
          (by simp)
    simpa [cutoff] using Nat.lt_succ_of_le hLe
  have hShell :=
    FiniteDistanceShellGeometricSum.sum_pow_distance_eq_shell_sum
      distance cutoff hDistance q
  have hSummable :=
    summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass
      C q hqNonneg hqLtOne
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        C * q ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) =
      C * (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        q ^ distance source) := by
          simp [distance, Finset.mul_sum]
    _ = C * (∑ m ∈ Finset.range cutoff,
        (((Finset.univ.filter fun source :
            PeriodicHypercubicEvenSpatialSliceLink H =>
              distance source = m).card : ℝ) * q ^ m)) := by
          rw [hShell]
    _ = ∑ m ∈ Finset.range cutoff,
        C * ((((Finset.univ.filter fun source :
            PeriodicHypercubicEvenSpatialSliceLink H =>
              distance source = m).card : ℝ) * q ^ m)) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.range cutoff,
        physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant m *
          (C * q ^ m) := by
          apply Finset.sum_le_sum
          intro m _hm
          have hCard :
              (((Finset.univ.filter fun source :
                  PeriodicHypercubicEvenSpatialSliceLink H =>
                    distance source = m).card : ℝ)) ≤
                physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant m := by
            simpa [distance, physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell] using
              physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_real_le_majorant
                H m
          calc
            C * ((((Finset.univ.filter fun source :
                PeriodicHypercubicEvenSpatialSliceLink H =>
                  distance source = m).card : ℝ) * q ^ m)) =
                (((Finset.univ.filter fun source :
                    PeriodicHypercubicEvenSpatialSliceLink H =>
                      distance source = m).card : ℝ)) *
                  (C * q ^ m) := by ring
            _ ≤ physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant m *
                  (C * q ^ m) :=
              mul_le_mul_of_nonneg_right hCard
                (mul_nonneg hC (pow_nonneg hqNonneg m))
    _ ≤ ∑' m : ℕ,
        physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant m *
          (C * q ^ m) := by
          exact hSummable.sum_le_tsum (Finset.range cutoff)
            (fun m _hm =>
              mul_nonneg
                (physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_nonneg m)
                (mul_nonneg hC (pow_nonneg hqNonneg m)))
    _ = physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass C q := rfl

/-- For s > 1, the actual posterior absolute covariance mass between any fixed
primary seed link and all radius-two-exterior source links is bounded by the
same H-independent completed seed-shell mass. -/
theorem physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovarianceMass_le
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
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H 2 beta B source (sourceValue source))|) ≤
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta)
        s⁻¹ := by
  classical
  have hsWeak : 1 ≤ s := hs.le
  have hsPos : 0 < s := lt_trans zero_lt_one hs
  have hInvNonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hsPos.le
  have hInvLtOne : s⁻¹ < 1 := inv_lt_one_of_one_lt hs
  have hPrefactor :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor_nonneg
      H 2 specialUnitaryTwoWilsonRankPositive s hsWeak beta hbeta hcut
  have hPointwise :
      (∑ source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2,
        |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
              H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g)
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
              H 2 beta B source (sourceValue source))|) ≤
        ∑ source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
              s beta *
            (s⁻¹) ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
    apply Finset.sum_le_sum
    intro source hSource
    have hCov :=
      physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovariance_abs_le_seedDistancePower
        H s hsWeak beta hbeta hcut B source (sourceValue source) g k hSource
    simpa [div_eq_mul_inv] using hCov
  have hFarToAll :
      (∑ source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
              s beta *
            (s⁻¹) ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) ≤
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
              s beta *
            (s⁻¹) ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ (physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2))
        (fun source _hUniv _hNotFar =>
          mul_nonneg hPrefactor
            (pow_nonneg hInvNonneg
              (physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source)))
  exact hPointwise.trans (hFarToAll.trans
    (physicalYangMillsSU2PrimaryPlaquetteSeedDistance_sum_geometric_le_mass
      H
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
        s beta)
      s⁻¹ hPrefactor hInvNonneg hInvLtOne))

end

end MathlibAnalytic
end MGAP4D
