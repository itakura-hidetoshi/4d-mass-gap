import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFirstCrossHarnackStationarityBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalUpdatedVarianceGenuineResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateKernelSectionExplicitMarkovKernel
import Mathlib.Tactic

/-!
# Vacuum-integrated first-cross energy controlled by the genuine target residual

PR #4795 proves, at one fixed outer background, the sharp decomposition

  firstCross
    <= K_H(beta) * updatedReferenceVariance
       + ofReal(||ResponseL2||^2).

PR #4798 identifies the physical-vacuum average of the diagonal
updated-reference variance with the canonical genuine target variance and
bounds it with coefficient one by the genuine target CondExpL2 residual.

This file composes those two results.  The only small measure-theoretic issue is
splitting the vacuum lower integral of

  K_H * variance(C) + responseSq(C).

We prove only the variance summand a.e.-measurable, by identifying it
vacuum-a.e. with the measurable canonical genuine residual energy under the
explicit kernel-section Markov kernel.  Thus no outer measurability theorem for
the response norm is required.

The resulting estimate is

  vacuumFirstCross
    <= K_H(beta) * ofReal(||F - CondExp_target F||^2)
       + vacuumIntegral(ofReal(||ResponseL2(C)||^2)).

No new Harnack factor, factor two, response coefficient, remote-separation
hypothesis, or finite-cardinality loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance vacuumFirstCrossGenuineResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumFirstCrossGenuineResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumFirstCrossGenuineResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumFirstCrossGenuineResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumFirstCrossGenuineResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumFirstCrossGenuineResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The diagonal updated-reference variance outer function is a.e.-measurable
under the physical vacuum law.

The measurable representative is the canonical genuine target residual energy
through the explicit fixed-right kernel-section Markov kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_referenceUpdatedBackgroundVariance_outer_aemeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    AEMeasurable
      (fun C =>
        ∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source) F C A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta C source distinguishedSource
            (C distinguishedSource) (C source))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
      H N hN beta hbeta
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_isMarkovKernel
      H N hN beta hbeta
  let center :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
      H N hN beta hbeta target F
  let outer :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
      H N target
  let Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((F z - center (outer z)) ^ 2)
  let canonicalVariance :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C => ∫⁻ A, Phi (C, A) ∂κ C
  let diagonalVariance :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ∫⁻ A,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source) F C A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source)
  have hCenter : StronglyMeasurable center := by
    simpa [center] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_stronglyMeasurable
        H N hN beta hbeta target F hF
  have hOuter : Measurable outer := by
    simpa [outer] using
      measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
        H N target
  have hResidual :
      StronglyMeasurable (fun z => F z - center (outer z)) :=
    hF.sub (hCenter.comp_measurable hOuter)
  have hPhi : Measurable Phi := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (hResidual.measurable.pow_const 2)
  have hCanonicalVariance : Measurable canonicalVariance := by
    have h :=
      hPhi.lintegral_kernel_prod_right'
        (κ := κ)
    simpa [canonicalVariance] using h
  have hCanonical :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_vacuum_kernelSection
      H N hN beta hbeta target source F hF
  have hVarianceAE : diagonalVariance =ᵐ[ν] canonicalVariance := by
    filter_upwards [hCanonical] with C hC
    have hDiag :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_kernelSectionFluctuation_sq_lintegral
        H N hN beta hbeta C distinguishedSource source target
        F hF bound hbound
    calc
      diagonalVariance C =
        ∫⁻ A,
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta C target source target
                (C source) (C target)
                (fun D => F (C, D)) A) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C := by
        simpa [diagonalVariance] using hDiag
      _ =
        ∫⁻ A, Phi (C, A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C := by
        apply lintegral_congr_ae
        filter_upwards [hC] with A hA
        have hA' :
            F (C, A) - center (outer (C, A)) =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
                H N hN beta hbeta C target source target
                (C source) (C target) (fun D => F (C, D)) A := by
          simpa [
            center, outer,
            periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap] using hA
        exact
          congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) hA'.symm
      _ = canonicalVariance C := by
        simp [
          canonicalVariance, κ,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_apply]
  exact
    hCanonicalVariance.aemeasurable.congr hVarianceAE.symm

/-- Vacuum-integrated first-cross energy is controlled by the genuine target
CondExpL2 residual plus the vacuum integral of the exact response-L2
norm-square. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_firstCrossEnergy_lintegral_le_harnackLawFactor_mul_condExpL2_residual_norm_sq_add_responseL2_norm_sq_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      (∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) +
      (∫⁻ C,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              F hF bound hbound C 0‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta
  let K : ℝ≥0∞ :=
    ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)
  let firstCross :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
  let variance :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ∫⁻ A,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source) F C A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source)
  let responseSq :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C 0‖ ^ 2)
  let targetResidualSq : ℝ≥0∞ :=
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound)‖ ^ 2)
  have hPoint : ∀ C, firstCross C ≤ K * variance C + responseSq C := by
    intro C
    simpa [firstCross, K, variance, responseSq] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_le_harnackLawFactor_mul_reference_updatedBackgroundVarianceEnergy_lintegral_add_responseL2_norm_sq_ofReal
        H N hN beta hbeta C distinguishedSource source target hne
        (C distinguishedSource) (C source) F hF bound hbound C
  have hVarianceAE : AEMeasurable variance ν := by
    simpa [variance, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_referenceUpdatedBackgroundVariance_outer_aemeasurable
        H N hN beta hbeta distinguishedSource source target
        F hF bound hbound
  have hScaledVarianceAE :
      AEMeasurable (fun C => K * variance C) ν :=
    hVarianceAE.const_mul K
  have hVarianceBound :
      (∫⁻ C, variance C ∂ν) ≤ targetResidualSq := by
    simpa [variance, ν, targetResidualSq] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_referenceUpdatedBackgroundVarianceEnergy_lintegral_le_condExpL2_residual_norm_sq
        H N hN beta hbeta distinguishedSource source target
        F hF bound hbound
  have hIntegrated :
      (∫⁻ C, firstCross C ∂ν) ≤
        ∫⁻ C, K * variance C + responseSq C ∂ν :=
    lintegral_mono hPoint
  have hSplit :
      (∫⁻ C, K * variance C + responseSq C ∂ν) =
        K * (∫⁻ C, variance C ∂ν) +
          ∫⁻ C, responseSq C ∂ν := by
    rw [lintegral_add_left' hScaledVarianceAE]
    rw [lintegral_const_mul'' K hVarianceAE]
  have hScaledVarianceBound :
      K * (∫⁻ C, variance C ∂ν) ≤ K * targetResidualSq :=
    mul_le_mul_right hVarianceBound K
  calc
    (∫⁻ C,
      (∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ C, firstCross C ∂ν := by
        rfl
    _ ≤ ∫⁻ C, K * variance C + responseSq C ∂ν :=
      hIntegrated
    _ = K * (∫⁻ C, variance C ∂ν) +
          ∫⁻ C, responseSq C ∂ν :=
      hSplit
    _ ≤ K * targetResidualSq +
          ∫⁻ C, responseSq C ∂ν :=
      add_le_add hScaledVarianceBound (le_refl _)
    _ =
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) +
        (∫⁻ C,
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                F hF bound hbound C 0‖ ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta) := by
      rfl

end

end MGAP4D.MathlibAnalytic
