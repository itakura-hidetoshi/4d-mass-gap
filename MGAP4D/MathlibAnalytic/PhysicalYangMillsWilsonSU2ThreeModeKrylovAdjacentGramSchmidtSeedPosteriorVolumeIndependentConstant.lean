import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorExplicitFourLinkResolvent
import Mathlib.Tactic

/-!
# Volume-independent Gram--Schmidt seed constant

PR #5250 computes the exact declared posterior variation of the canonical
primary-plaquette Gram--Schmidt seed as

  8 * ||O_{H,mode}||.

The observable O_{H,mode} is just the fixed SU(2) Gram--Schmidt class function
composed with the primary spatial plaquette holonomy.  Composition cannot
increase the sup norm.  Hence

  ||O_{H,mode}|| <= ||phi_mode||_infty,

where phi_mode is a bounded-continuous function on SU(2) depending only on the
mode index.

Substituting this estimate removes the remaining finite-volume symbol H from
the canonical strict-resolvent constants.

No covariance/L2-coordinate identification, positive-depth hard support, or
new physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3VolumeIndependentSeedConstantTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3VolumeIndependentSeedConstantCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3VolumeIndependentSeedConstantSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3VolumeIndependentSeedConstantMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3VolumeIndependentSeedConstantBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3VolumeIndependentSeedConstantSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The theorem-generated continuous SU(2) Gram--Schmidt mode, viewed as a
bounded-continuous class function on the compact group. -/
noncomputable def
    specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
    (mode : ℕ) :
    BoundedContinuousFunction (Matrix.specialUnitaryGroup (Fin 2) ℂ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode mode)

/-- Pullback along the primary plaquette holonomy cannot increase the sup norm.
This is the exact step that removes H from the seed-size constant. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_norm_le_modeNorm
    (H mode : ℕ) :
    ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
        H mode‖ ≤
      ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
        mode‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
  intro A
  change
    ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode mode
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))‖ ≤
      ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
        mode‖
  exact
    BoundedContinuousFunction.norm_coe_le_norm
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode mode)
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))

/-- The exact four-link variation total is bounded by a constant depending
only on the SU(2) Gram--Schmidt mode. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile_total_le_eight_modeNorm
    (H mode : ℕ) :
    finiteProductVariationTotal
        (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
          H mode).variation ≤
      8 *
        ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
          mode‖ := by
  rw [
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile_total_eq_eight_norm
      H mode
  ]
  exact
    mul_le_mul_of_nonneg_left
      (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_norm_le_modeNorm
        H mode)
      (by norm_num)

/-- Canonical high-temperature Gram--Schmidt seed covariance bound with a
constant independent of H. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_canonicalUniformVolumeIndependent
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
            ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
              mode‖)) := by
  have hBase :=
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_canonicalUniformExplicitFourLinkResolvent
      H mode s hs beta hbeta hbetaCutoff B source sourceValue
  have hNorm :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_norm_le_modeNorm
      H mode
  have hRadius :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2 := by
    exact div_nonneg
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta)
      (by norm_num)
  have hCoeff :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta < 1 :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
      s hs beta hbeta hbetaCutoff
  have hGapInv :
      0 ≤
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hCoeff.le)
  have hEight :
      8 *
          ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
            H mode‖ ≤
        8 *
          ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
            mode‖ :=
    mul_le_mul_of_nonneg_left hNorm (by norm_num)
  have hInner :=
    mul_le_mul_of_nonneg_left hEight hGapInv
  have hOuter :=
    mul_le_mul_of_nonneg_left hInner hRadius
  exact hBase.trans hOuter

/-- Matching source-retilt response bound with the same H-independent seed
constant. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_canonicalUniformVolumeIndependent
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
            ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
              mode‖))) /
      Real.exp (-8 * beta) := by
  have hBase :=
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_canonicalUniformExplicitFourLinkResolvent
      H mode s hs beta hbeta hbetaCutoff B source sourceValue
  have hNorm :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable_norm_le_modeNorm
      H mode
  have hRadius :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2 := by
    exact div_nonneg
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta)
      (by norm_num)
  have hCoeff :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta < 1 :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
      s hs beta hbeta hbetaCutoff
  have hGapInv :
      0 ≤
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hCoeff.le)
  have hEight :
      8 *
          ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
            H mode‖ ≤
        8 *
          ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtBoundedMode
            mode‖ :=
    mul_le_mul_of_nonneg_left hNorm (by norm_num)
  have hInner :=
    mul_le_mul_of_nonneg_left hEight hGapInv
  have hOuter :=
    mul_le_mul_of_nonneg_left hInner hRadius
  exact
    hBase.trans
      (div_le_div_of_nonneg_right hOuter (Real.exp_pos _).le)

end

end MathlibAnalytic
end MGAP4D
