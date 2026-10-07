import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorSourceTiltCovarianceFactorization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack
import Mathlib.Tactic

/-!
# Seed-distance covariance decay for the source-only joint-response tilt

PR #5234 factors the full posterior right-target local factor as a positive
source-independent boundary factor times the source-only tilt used by the signed
joint-kernel response.

The boundary factor is the exponential of one half of a spatial Wilson-action
link update.  At most six spatial plaquettes touch one link and each plaquette
energy changes by at most two.  Hence its logarithmic increment has absolute
value at most six, uniformly in the periodic volume:

  exp(-6 beta) <= boundaryTilt <= exp(6 beta).

Therefore its inverse is at most exp(6 beta).  Combining this with the exact
covariance scaling from #5234 and the seed-distance full-local-factor decay from
#5228 transfers the spatial decay to the literal source-only tilt appearing in
the signed source response.

No source-coordinate L2 norm is identified with covariance in this file.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryIncrement_abs_le_six
    (H N : ℕ)
    (hN : 0 < N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |(1 / 2 : ℝ) *
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update B target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p))| ≤ 6 := by
  classical
  let s := periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target
  let d := fun p : PeriodicHypercubicEvenSpatialSlicePlaquette H =>
    specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update B target g) p) -
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)
  have hSum : |∑ p ∈ s, d p| ≤ 12 := by
    calc
      |∑ p ∈ s, d p| ≤ ∑ p ∈ s, |d p| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ s, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact specialUnitaryWilsonPlaquetteEnergy_sub_abs_le_two N hN _ _
      _ = (s.card : ℝ) * 2 := by simp
      _ ≤ (6 : ℝ) * 2 := by
        gcongr
        exact_mod_cast
          periodicHypercubicEvenSpatialSliceTouchingPlaquettes_card_le_six H target
      _ = 12 := by norm_num
  change |(1 / 2 : ℝ) * ∑ p ∈ s, d p| ≤ 6
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |∑ p ∈ s, d p| ≤ (1 / 2 : ℝ) * 12 :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = 6 := by norm_num

theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt_exp_neg_six_mul_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-6 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
        H N beta B target g := by
  have hd :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryIncrement_abs_le_six
      H N hN B target g
  have hdle :
      (1 / 2 : ℝ) *
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                (Function.update B target g) p) -
            specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)) ≤ 6 :=
    (abs_le.mp hd).2
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hdle hbeta
  nlinarith

theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt_le_exp_six_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
        H N beta B target g ≤
      Real.exp (6 * beta) := by
  have hd :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryIncrement_abs_le_six
      H N hN B target g
  have hdge :
      (-6 : ℝ) ≤
        (1 / 2 : ℝ) *
          ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
            (specialUnitaryWilsonPlaquetteEnergy N
                (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                  (Function.update B target g) p) -
              specialUnitaryWilsonPlaquetteEnergy N
                (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)) :=
    (abs_le.mp hd).1
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hdge hbeta
  nlinarith

theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt_inv_le_exp_six_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
        H N beta B target g)⁻¹ ≤
      Real.exp (6 * beta) := by
  have hd :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryIncrement_abs_le_six
      H N hN B target g
  have hdle :
      (1 / 2 : ℝ) *
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                (Function.update B target g) p) -
            specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)) ≤ 6 :=
    (abs_le.mp hd).2
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
  rw [← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hdle hbeta
  nlinarith

/-- The seed-to-remote covariance decay from #5228 transferred to the literal
source-only tilt used in the signed joint response. -/
theorem physicalYangMillsSU2PrimaryPlaquetteSeed_sourceRightLinkTiltCovariance_abs_le_seedDistancePower
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
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
          H 2 beta B source sourceValue)| ≤
      Real.exp (6 * beta) *
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta /
          s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) := by
  let F :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g
  let Gfull :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H 2 beta B source sourceValue
  let Gsrc :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
      H 2 beta B source sourceValue
  let c :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt
      H 2 beta B source sourceValue
  let covFull :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B F Gfull
  let covSrc :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B F Gsrc
  have hFull :
      |covFull| ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta /
          s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source := by
    simpa [covFull, F, Gfull] using
      physicalYangMillsSU2PrimaryPlaquetteSeed_localFactorCovariance_abs_le_seedDistancePower
        H s hs beta hbeta hcut B source sourceValue g k hFar
  have hScale : covFull = c * covSrc := by
    simpa [covFull, covSrc, F, Gfull, Gsrc, c] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_localFactor_eq_boundaryTilt_mul_sourceRightLinkTilt
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B F source sourceValue
  have hcPos : 0 < c := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt_pos
        H 2 beta B source sourceValue
  have hcInv :
      c⁻¹ ≤ Real.exp (6 * beta) := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetBoundaryTilt_inv_le_exp_six_mul
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B source sourceValue
  have hCovSrc : covSrc = c⁻¹ * covFull := by
    rw [hScale]
    field_simp [hcPos.ne']
  have hPrefactor :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor_nonneg
      H 2 specialUnitaryTwoWilsonRankPositive s hs beta hbeta hcut
  have hsPos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hBoundNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta /
          s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source :=
    div_nonneg hPrefactor (pow_pos hsPos _).le
  change |covSrc| ≤ _
  rw [hCovSrc, abs_mul, abs_of_nonneg (inv_nonneg.mpr hcPos.le)]
  calc
    c⁻¹ * |covFull| ≤ c⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta /
          s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) :=
      mul_le_mul_of_nonneg_left hFull (inv_nonneg.mpr hcPos.le)
    _ ≤ Real.exp (6 * beta) *
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta /
          s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) :=
      mul_le_mul_of_nonneg_right hcInv hBoundNonneg

theorem physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_sourceRightLinkTiltCovariance_abs_le_seedDistancePower
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
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabSourceRightLinkTiltBCF
          H 2 beta B source sourceValue)| ≤
      Real.exp (6 * beta) *
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
            s beta /
          s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) := by
  exact
    physicalYangMillsSU2PrimaryPlaquetteSeed_sourceRightLinkTiltCovariance_abs_le_seedDistancePower
      H s hs beta hbeta hcut B source sourceValue g k
      ((physicalYangMillsSU2PrimaryPlaquette_mem_farLinks H 2 source).mp hFar)

end

end MathlibAnalytic
end MGAP4D
