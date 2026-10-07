import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorStrictResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalVolumeUniformDobrushinCutoff
import Mathlib.Tactic

/-!
# Canonical volume-uniform strict resolvent for the Gram--Schmidt seed

PR #5248 proves terminal-free posterior covariance and source-retilt bounds
from an arbitrary nonstrict posterior influence matrix together with a strict
row coefficient.

The existing canonical fixed-right bootstrap route already supplies exactly
that strictness, uniformly in the finite spatial side and rank, on a positive
high-temperature interval.  This file composes those theorem artifacts.

For every exponential scale s > 8 and every coupling below the existing
volume-uniform canonical Dobrushin cutoff, the explicit assumptions

* a posterior influence datum D;
* a nonnegative row coefficient;
* strictness of that coefficient;
* all row-sum bounds

disappear from the Gram--Schmidt seed interface.  The remaining resolvent
coefficient is the already-defined H- and N-independent scalar

  alpha_bar(s,beta)
    = canonicalFixedRightBootstrapUniformCoefficient(s,beta).

No covariance/L2-coordinate identification, hard support at positive Krylov
depth, or new physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3CanonicalUniformSeedResolventTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3CanonicalUniformSeedResolventCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3CanonicalUniformSeedResolventSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3CanonicalUniformSeedResolventMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3CanonicalUniformSeedResolventBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3CanonicalUniformSeedResolventSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3CanonicalUniformSeedResolventSpatialLinkNonempty (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) := by
  refine ⟨
    (⟨(0 : PeriodicHypercubicEvenVertex H), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨(1 : PeriodicHypercubicAxis), by decide⟩)⟩

/-- The coefficient carried by the selected volume-uniform canonical
Dobrushin data is definitionally the explicit H- and N-independent uniform
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_coefficient
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
        H N hN s hs beta hbeta hbetaCutoff B).coefficient =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta := by
  rfl

/-- Terminal-free Gram--Schmidt seed covariance bound with all strict-row
hypotheses discharged by the existing canonical volume-uniform Dobrushin
cutoff. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_canonicalUniformStrictResolvent
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
          finiteProductVariationTotal
            (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).variation) := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H 2 specialUnitaryTwoWilsonRankPositive s hs beta hbeta hbetaCutoff B
  have hEdge :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos
  have h :=
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_strictResolvent
      H mode beta hbeta B source sourceValue
      D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      hEdge D.coefficient D.coefficient_nonneg D.coefficient_lt_one
      D.rowSum_le_coefficient
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_coefficient
      H 2 specialUnitaryTwoWilsonRankPositive s hs beta hbeta hbetaCutoff B
  ] at h
  exact h

/-- The matching source-retilt response bound on the same canonical
volume-uniform high-temperature interval. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_canonicalUniformStrictResolvent
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
          finiteProductVariationTotal
            (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).variation)) /
      Real.exp (-8 * beta) := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H 2 specialUnitaryTwoWilsonRankPositive s hs beta hbeta hbetaCutoff B
  have hEdge :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos
  have h :=
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_strictResolvent
      H mode beta hbeta B source sourceValue
      D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      hEdge D.coefficient D.coefficient_nonneg D.coefficient_lt_one
      D.rowSum_le_coefficient
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_coefficient
      H 2 specialUnitaryTwoWilsonRankPositive s hs beta hbeta hbetaCutoff B
  ] at h
  exact h

end

end MathlibAnalytic
end MGAP4D
