import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorCanonicalUniformStrictResolvent
import Mathlib.Tactic

/-!
# Explicit four-link strict resolvent for the Gram--Schmidt seed

PR #5249 removes all external strict-row assumptions from the bare
Gram--Schmidt seed covariance/source-retilt bounds by inserting the existing
canonical volume-uniform posterior Dobrushin data.

The only remaining abstract scalar there is the total declared coordinate
variation of the seed.  PR #5245 already proves that this variation is exactly

  2 * ||O||

on the four primary-plaquette seed links and zero elsewhere.  Therefore its
total finite variation is exactly

  4 * (2 * ||O||) = 8 * ||O||.

This file performs that finite sum and substitutes it into the canonical
strict-resolvent bounds.  The resulting constants are independent of the
finite spatial side H.

No positive-Krylov-depth support statement, covariance/L2 identification, or
new physical hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3ExplicitFourLinkResolventTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3ExplicitFourLinkResolventCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3ExplicitFourLinkResolventSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3ExplicitFourLinkResolventMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3ExplicitFourLinkResolventBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3ExplicitFourLinkResolventSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact total variation of the canonical primary-plaquette Gram--Schmidt
seed: four links, each with declared variation (2 ||O||). -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile_total_eq_eight_norm
    (H mode : ℕ) :
    finiteProductVariationTotal
        (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
          H mode).variation =
      8 *
        ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode‖ := by
  classical
  let S := physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet H
  let O :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
      H mode
  unfold finiteProductVariationTotal
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
        H mode).variation e) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        if e ∈ S then 2 * ‖O‖ else 0 := by
          apply Finset.sum_congr rfl
          intro e _he
          change
            (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound
              H mode).variation e =
              if e ∈ S then 2 * ‖O‖ else 0
          simpa [S, O] using
            physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorLinkVariationBound_variation
              H mode e
    _ =
      ∑ e ∈ S, 2 * ‖O‖ := by
        rw [← Finset.sum_filter]
        congr 1
        ext e
        simp
    _ = 8 * ‖O‖ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [physicalYangMillsSU2PrimaryPlaquetteSeedLinkSet_card]
      ring

/-- Fully explicit H-independent canonical strict-resolvent covariance bound
for the bare Gram--Schmidt seed. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_canonicalUniformExplicitFourLinkResolvent
    (H mode : ℕ)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode)| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta)⁻¹ *
          (8 *
            ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
              H mode‖)) := by
  have h :=
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_canonicalUniformStrictResolvent
      H mode s hs beta hbeta hbetaCutoff B source sourceValue
  rw [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile_total_eq_eight_norm
      H mode
  ] at h
  exact h

/-- Fully explicit source-retilt response bound for the same four-link seed. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_canonicalUniformExplicitFourLinkResolvent
    (H mode : ℕ)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    |(∫ A,
        periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode A
        ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B).tilted
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt
            H 2 beta B source sourceValue))) -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode)| ≤
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta)⁻¹ *
          (8 *
            ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
              H mode‖))) /
      Real.exp (-8 * beta) := by
  have h :=
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_canonicalUniformStrictResolvent
      H mode s hs beta hbeta hbetaCutoff B source sourceValue
  rw [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile_total_eq_eight_norm
      H mode
  ] at h
  exact h

end

end MathlibAnalytic
end MGAP4D
