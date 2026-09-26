import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSEnergySplit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFirstCrossEnergyReordered
import Mathlib.Tactic

/-!
# Transport the second-mean RMS first-energy summand to ordered first-cross energy

PR #4801 splits the exact second-mean RMS L2 energy into

  firstVarianceEnergyAtSecondMean + secondVarianceEnergy.

This file transports the first summand exactly.

At each source-pair point z, the first centered energy is a real integral of a
nonnegative square under the first target-fiber probability law. Boundedness
of the concrete representative and of the actual second-law mean gives L2
integrability of that fiber section, so ofReal of the real integral equals
the corresponding ENNReal lower integral exactly.

Tonelli for the source-pair target-fiber triple law then recovers the complete
first-cross energy, and PR #4780 reorders that law to the canonical ordered
carrier.

Thus

  ∫_{nu_source} ofReal(firstVarianceEnergyAtSecondMean)
    =
  ∫_{ordered} firstCrossEnergy.

No inequality, Harnack factor, factor two, response coefficient, or
cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance secondMeanRMSFirstCrossTransportSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSFirstCrossTransportSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSFirstCrossTransportSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSFirstCrossTransportSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSFirstCrossTransportSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSFirstCrossTransportSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pointwise conversion of the first centered real fiber energy to its exact
ENNReal target-fiber lower integral. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier_ofReal_eq_targetFiber_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left z) =
      ∫⁻ g,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
              H N target source F left
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
                H N hN beta hbeta B distinguishedSource source target k g₂
                F left z)
              (z, g)) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
          H N hN beta hbeta B distinguishedSource source target k g₂ z := by
  let mean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left z
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
      H N hN beta hbeta B distinguishedSource source target k g₂ z
  let fiberSection : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
        H N target source F left mean (z, g)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hMeanNorm :
      ‖mean‖ ≤ |bound| := by
    simpa [mean] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_norm_le_of_bounded
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left z
  have hMeanAbs : |mean| ≤ |bound| := by
    simpa [Real.norm_eq_abs] using hMeanNorm
  have hSectionStrong : StronglyMeasurable fiberSection := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_stronglyMeasurable
        H N target source F hF left mean).comp_measurable
        (measurable_const.prodMk measurable_id)
  have hSectionBound : ∀ g, ‖fiberSection g‖ ≤ 2 * |bound| := by
    intro g
    calc
      ‖fiberSection g‖ ≤ |bound| + |mean| := by
        simpa [fiberSection] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_norm_le
            H N target source F bound hbound left mean (z, g)
      _ ≤ |bound| + |bound| := add_le_add (le_refl _) hMeanAbs
      _ = 2 * |bound| := by ring
  have hLp : MemLp fiberSection 2 μ :=
    MemLp.of_bound hSectionStrong.aestronglyMeasurable (2 * |bound|)
      (Filter.Eventually.of_forall hSectionBound)
  have hSqInt : Integrable (fun g => fiberSection g ^ 2) μ := by
    simpa only [Pi.pow_apply] using hLp.integrable_sq
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
  change
    ENNReal.ofReal (∫ g, fiberSection g ^ 2 ∂μ) =
      ∫⁻ g, ENNReal.ofReal (fiberSection g ^ 2) ∂μ
  exact
    ofReal_integral_eq_lintegral_ofReal hSqInt
      (ae_of_all μ fun g => sq_nonneg (fiberSection g))

/-- Exact outer transport of the first second-mean RMS energy summand to the
ordered first-cross law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier_lintegral_eq_orderedFirstCrossEnergy_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ z,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left z)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      ∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
  let mean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  let raw :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    fun zg =>
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
            H N target source F left (mean zg.1) zg) ^ 2)
  have hMean : StronglyMeasurable mean := by
    simpa [mean] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_stronglyMeasurable
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
  have hZero :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_stronglyMeasurable
      H N target source F hF left 0
  have hResidual :
      StronglyMeasurable
        (fun zg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
              H N target source F left 0 zg -
            mean zg.1) :=
    hZero.sub (hMean.comp_measurable measurable_fst)
  have hRaw : Measurable raw := by
    have hAlt :
        Measurable
          (fun zg :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                  Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
              Matrix.specialUnitaryGroup (Fin N) ℂ =>
            ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
                  H N target source F left 0 zg -
                mean zg.1) ^ 2)) :=
      ENNReal.continuous_ofReal.measurable.comp
        (hResidual.measurable.pow_const 2)
    have hEq :
        raw =
          (fun zg =>
            ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
                  H N target source F left 0 zg -
                mean zg.1) ^ 2)) := by
      funext zg
      simp [
        raw,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection]
    rw [hEq]
    exact hAlt
  calc
    (∫⁻ z,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left z)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      ∫⁻ z,
        ∫⁻ g, raw (z, g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
            H N hN beta hbeta B distinguishedSource source target k g₂ z
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
      apply lintegral_congr
      intro z
      simpa [raw, mean] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier_ofReal_eq_targetFiber_lintegral
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left z
    _ =
      ∫⁻ zg, raw zg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
      symm
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
      exact Measure.lintegral_compProd hRaw
    _ =
      ∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂ F left Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
      simpa [raw, mean] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCrossEnergy_lintegral_eq_ordered
          H N hN beta hbeta B distinguishedSource source target k g₂ F hF left

end

end MGAP4D.MathlibAnalytic
