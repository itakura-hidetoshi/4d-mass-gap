import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSL2
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

/-!
# Exact energy split for the second-mean source-pair RMS L2 vector

PR #4800 packages the exact RMS amplitude centered pointwise at the actual
second target-law fiber mean.

For an off-diagonal source/target pair, the square of that amplitude is exactly

  firstEnergyAtSecondMean + secondVarianceEnergy.

This file lifts that pointwise identity to the exact source-pair L2 norm:

  ofReal (||RMS2L2||^2)
    =
  ∫ ofReal(firstEnergyAtSecondMean)
    + ∫ ofReal(secondVarianceEnergy).

No law reordering is performed here.  The next theorem unit can therefore map
the two summands independently to the already-established ordered first-cross
and updated-variance laws.

No inequality, factor two, response coefficient, or cardinality factor is
introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance secondMeanRMSEnergySplitSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSEnergySplitSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSEnergySplitSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSEnergySplitSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSEnergySplitSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSEnergySplitSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise exact square identity for the RMS centered at the actual
second-law fiber mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_sq_eq_firstVariance_add_secondVariance
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left z) ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z := by
  let mean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left z
  have hFirst0 :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier,
      mean] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_nonneg
        H N hN beta hbeta B distinguishedSource source target k g₂ F left mean z
  have hSecond0 :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier,
      mean] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondCenteredEnergy_nonneg
        H N hN beta hbeta B distinguishedSource source target k g₂ F left mean z
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_eq_sqrt_centeredEnergy]
  simp only [hne, if_false]
  change
    (Real.sqrt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z)) ^ 2 =
      _
  rw [Real.sq_sqrt (add_nonneg hFirst0 hSecond0)]

/-- The squared L2 norm of the exact second-mean RMS is the real integral of
the sum of its two centered energies. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_eq_integral_firstVariance_add_secondVariance
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left‖ ^ 2 =
      ∫ z,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let amplitude :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
  have hRep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
  change ‖amplitude‖ ^ 2 = ∫ z, _ ∂ν
  rw [realL2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [hRep] with z hz
  rw [hz]
  have hAmp0 :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_nonneg
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
        z
  rw [Real.norm_eq_abs, abs_of_nonneg hAmp0]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_sq_eq_firstVariance_add_secondVariance
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F left z

/-- ENNReal form of the exact RMS energy split. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_ofReal_eq_firstVariance_lintegral_add_secondVariance_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left‖ ^ 2) =
      (∫⁻ z,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂) +
      (∫⁻ z,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂) := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let firstEnergy :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  let secondEnergy :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  let amplitudeOnCarrier :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  have hAmplitudeLp :
      MemLp amplitudeOnCarrier 2 ν := by
    simpa [amplitudeOnCarrier, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_memLp_two_of_bounded
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left
  have hSumEq : ∀ z, amplitudeOnCarrier z ^ 2 = firstEnergy z + secondEnergy z := by
    intro z
    simpa [amplitudeOnCarrier, firstEnergy, secondEnergy] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_sq_eq_firstVariance_add_secondVariance
        H N hN beta hbeta B distinguishedSource source target hne k g₂ F left z
  have hSumInt :
      Integrable (fun z => firstEnergy z + secondEnergy z) ν := by
    exact hAmplitudeLp.integrable_sq.congr
      (ae_of_all ν fun z => hSumEq z)
  have hSum0 : ∀ z, 0 ≤ firstEnergy z + secondEnergy z := by
    intro z
    have hFirst0 :
        0 ≤ firstEnergy z := by
      simpa [firstEnergy] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_nonneg
          H N hN beta hbeta B distinguishedSource source target k g₂ F left
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
          z
    have hSecond0 :
        0 ≤ secondEnergy z := by
      simpa [secondEnergy] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondCenteredEnergy_nonneg
          H N hN beta hbeta B distinguishedSource source target k g₂ F left
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
          z
    exact add_nonneg hFirst0 hSecond0
  have hFirstStrong : StronglyMeasurable firstEnergy := by
    simpa [firstEnergy] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier_stronglyMeasurable
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
  have hSecondStrong : StronglyMeasurable secondEnergy := by
    simpa [secondEnergy] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier_stronglyMeasurable
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
  have hFirst0 : ∀ z, 0 ≤ firstEnergy z := by
    intro z
    simpa [firstEnergy] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy_nonneg
        H N hN beta hbeta B distinguishedSource source target k g₂ F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
        z
  have hSecond0 : ∀ z, 0 ≤ secondEnergy z := by
    intro z
    simpa [secondEnergy] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondCenteredEnergy_nonneg
        H N hN beta hbeta B distinguishedSource source target k g₂ F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
        z
  have hNorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_eq_integral_firstVariance_add_secondVariance
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F hF bound hbound left
  calc
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left‖ ^ 2) =
      ENNReal.ofReal (∫ z, firstEnergy z + secondEnergy z ∂ν) := by
        rw [hNorm]
    _ =
      ∫⁻ z, ENNReal.ofReal (firstEnergy z + secondEnergy z) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hSumInt (ae_of_all ν hSum0)
    _ =
      ∫⁻ z,
        (ENNReal.ofReal (firstEnergy z) +
          ENNReal.ofReal (secondEnergy z)) ∂ν := by
        apply lintegral_congr
        intro z
        rw [ENNReal.ofReal_add (hFirst0 z) (hSecond0 z)]
    _ =
      (∫⁻ z, ENNReal.ofReal (firstEnergy z) ∂ν) +
        ∫⁻ z, ENNReal.ofReal (secondEnergy z) ∂ν := by
        exact
          lintegral_add_left'
            (μ := ν)
            (f := fun z => ENNReal.ofReal (firstEnergy z))
            (ENNReal.continuous_ofReal.measurable.comp
              hFirstStrong.measurable).aemeasurable
            (fun z => ENNReal.ofReal (secondEnergy z))
    _ = _ := by
      rfl

end

end MGAP4D.MathlibAnalytic
