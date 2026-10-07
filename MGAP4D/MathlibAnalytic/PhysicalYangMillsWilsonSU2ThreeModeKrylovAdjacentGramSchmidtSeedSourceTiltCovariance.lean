import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorVariation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorLocalCovarianceFiniteTelescope
import Mathlib.Tactic

/-!
# Generic posterior source re-tilt and Gram--Schmidt seed covariance bridge

The canonical source-retilt identity in the posterior development was stated
for a target-local Wilson factor.  Its proof, however, uses only the exact
Radon--Nikodym multiplier of the source update.  This file records the
corresponding identity for an arbitrary bounded-continuous observable O:

  E_{pi_B tilted by source}[O] - E_{pi_B}[O]
    = Cov_{pi_B}(L_source, O) / E_{pi_B}[L_source].

The source-factor mean has the existing lower bound exp(-8 beta), so any
covariance bound immediately yields a source-response bound with the exact
same denominator.

The second layer turns the existing finite covariance telescope into a bound
on the covariance itself:

  |Cov(L_source,O)|
    <= (width(beta)/2) * finiteResolvent(source)
       + |terminal covariance|.

Finally this is specialized to the four-link primary-plaquette Gram--Schmidt
seed profile from PR #5245.  This is the correct posterior interface for the
bare seed observable; it does not identify the seed with one local Boltzmann
factor, does not identify covariance with an L2 coordinate norm, and does not
assert hard support for positive Krylov depth.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3GenericSeedCovarianceTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3GenericSeedCovarianceCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3GenericSeedCovarianceSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3GenericSeedCovarianceMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3GenericSeedCovarianceBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3GenericSeedCovarianceSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact source re-tilt/covariance identity for an arbitrary
bounded-continuous posterior observable.  The covariance is oriented with the
source local factor in the left slot, matching the generic covariance
telescope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedBCFExpectation_sub_mean_eq_covariance_div_sourceMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    (∫ A,
        O A
        ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B).tilted
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt
            H N beta B source sourceValue))) -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B O =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue)
          O /
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let Z : ℝ := ∫ A, L A ∂mu
  have hZLower :
      Real.exp (-8 * beta) ≤ Z := by
    simpa [Z, mu, L,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_exp_neg_eight_mul_le
        H N hN beta hbeta B source sourceValue
  have hZPos : 0 < Z :=
    lt_of_lt_of_le (Real.exp_pos _) hZLower
  have hZNe : Z ≠ 0 := ne_of_gt hZPos
  have hTilt :
      (∫ A,
          O A
          ∂(mu.tilted
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt
              H N beta B source sourceValue))) =
        (∫ A, L A * O A ∂mu) / Z := by
    rw [MeasureTheory.integral_tilted]
    simp_rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt,
      Real.exp_log
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
          H N beta _ B source sourceValue),
      smul_eq_mul]
    change
      (∫ A, (L A / Z) * O A ∂mu) =
        (∫ A, L A * O A ∂mu) / Z
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div]
  rw [hTilt]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    (∫ A, L A * O A ∂mu) / Z - (∫ A, O A ∂mu) =
      ((∫ A, L A * O A ∂mu) -
        (∫ A, L A ∂mu) * (∫ A, O A ∂mu)) / Z
  change
    (∫ A, L A * O A ∂mu) / Z - (∫ A, O A ∂mu) =
      ((∫ A, L A * O A ∂mu) -
        Z * (∫ A, O A ∂mu)) / Z
  field_simp [hZNe]

/-- An absolute covariance bound gives the corresponding arbitrary-observable
source re-tilt response bound, with the exact posterior source-mean floor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedBCFExpectation_sub_mean_abs_le_of_covariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (K : ℝ)
    (hK : 0 ≤ K)
    (hCov :
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue)
          O| ≤ K) :
    |(∫ A,
        O A
        ∂((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
            H N hN beta hbeta B).tilted
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt
            H N beta B source sourceValue))) -
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B O| ≤
      K / Real.exp (-8 * beta) := by
  let sourceMean :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
  let cov :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
      O
  have hMeanLower :
      Real.exp (-8 * beta) ≤ sourceMean := by
    simpa [sourceMean] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_exp_neg_eight_mul_le
        H N hN beta hbeta B source sourceValue
  have hm : 0 < Real.exp (-8 * beta) := Real.exp_pos _
  have hMeanPos : 0 < sourceMean :=
    lt_of_lt_of_le hm hMeanLower
  have hIdentity :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedBCFExpectation_sub_mean_eq_covariance_div_sourceMean
      H N hN beta hbeta B source sourceValue O
  rw [hIdentity]
  change |cov / sourceMean| ≤ K / Real.exp (-8 * beta)
  rw [abs_div, abs_of_pos hMeanPos]
  apply (div_le_div_iff₀ hMeanPos hm).2
  calc
    |cov| * Real.exp (-8 * beta) ≤
        K * Real.exp (-8 * beta) :=
      mul_le_mul_of_nonneg_right
        (by simpa [cov] using hCov) hm.le
    _ ≤ K * sourceMean :=
      mul_le_mul_of_nonneg_left hMeanLower hK

/-- The generic finite covariance telescope controls the covariance itself by
its finite-resolvent contribution plus the terminal covariance remainder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_finiteResolvent_add_terminal
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (M : ℕ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        O| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D P.variation M source +
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        (((P.toRandomScanCenteredState).randomScanIterate D M).observable)| := by
  let c0 :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
      O
  let cM :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
      (((P.toRandomScanCenteredState).randomScanIterate D M).observable)
  let R :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta / 2) *
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        D P.variation M source
  have hDiff : |c0 - cM| ≤ R := by
    simpa [c0, cM, R] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScanCenteredState_partial_telescope_abs_le_finiteResolventProfile
        source sourceValue P D hEdge M
  calc
    |c0| = |(c0 - cM) + cM| := by
      congr 1
      ring
    _ ≤ |c0 - cM| + |cM| := abs_add _ _
    _ ≤ R + |cM| := add_le_add_right hDiff _
    _ = _ := by rfl

/-- Specialization of the generic covariance/resolvent bridge to the actual
four-link primary-plaquette Gram--Schmidt seed observable. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_finiteResolvent_add_terminal
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (M : ℕ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode)| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D
          (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
            H mode).variation
          M source +
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)
        ((((physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).toRandomScanCenteredState).randomScanIterate D M).observable)| := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_finiteResolvent_add_terminal
      source sourceValue
      (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile H mode)
      D hEdge M

/-- The corresponding source-retilt response of the bare Gram--Schmidt seed is
bounded by the same resolvent-plus-terminal envelope divided by the exact
source-mean floor exp(-8 beta). -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_sourceTiltedExpectation_sub_mean_abs_le_finiteResolvent_add_terminal
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (M : ℕ) :
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
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D
          (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
            H mode).variation
          M source +
        |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H 2 beta B source sourceValue)
          ((((physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
                H mode).toRandomScanCenteredState).randomScanIterate D M).observable)|) /
      Real.exp (-8 * beta) := by
  let O :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
      H mode
  let K :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta / 2) *
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        D
        (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
          H mode).variation
        M source +
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)
        ((((physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).toRandomScanCenteredState).randomScanIterate D M).observable)|
  have hCov :
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H 2 beta B source sourceValue)
          O| ≤ K := by
    simpa [O, K] using
      physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_finiteResolvent_add_terminal
        H mode beta hbeta B source sourceValue D hEdge M
  have hK : 0 ≤ K :=
    (abs_nonneg
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)
        O)).trans hCov
  simpa [O, K] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedBCFExpectation_sub_mean_abs_le_of_covariance
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
      source sourceValue O K hK hCov

end

end MathlibAnalytic
end MGAP4D
