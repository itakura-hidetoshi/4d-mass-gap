import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseResidualVacuumBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumSecondMeanRMSTargetMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalResidualVacuumKernelSectionAE
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# Vacuum exchange for the link-indexed target residual sum

PR #4845 leaves the finite target sum inside the outer physical-vacuum
lintegral. To exchange that finite sum without a cardinality loss, we first
prove the required vacuum-a.e. measurability of each fixed-target residual
energy.

The measurability proof uses the explicit fixed-right Markov kernel already
constructed in the genuine joint disintegration spine. The literal
kernel-section residual is vacuum/kernel-section a.e. equal to the canonical
fiber-mean residual, whose joint square is measurable. Hence each target
residual energy has a measurable Markov-kernel representative.

Mathlib finite additivity can then be applied exactly:

  integral_C sum_target E_target(C,target)
    = sum_target integral_C E_target(C,target)
    = sum_target CanonicalFiberVariance(target).

Combining this identity with PR #4845 gives the volume-uniform global response
energy bound by the genuine canonical target fiber variances. A final
coefficient-one comparison replaces those variances by the genuine
conditional-expectation residual norm-squares.

No finite-cardinality factor, response symmetry, or new probability law is
introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance targetResidualVacuumSumSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance targetResidualVacuumSumSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance targetResidualVacuumSumSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance targetResidualVacuumSumSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance targetResidualVacuumSumSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance targetResidualVacuumSumSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For a strongly measurable bounded concrete observable, the fixed-target
kernel-section residual energy is a.e. measurable under the physical vacuum.

The measurable representative is obtained by integrating the measurable
canonical fiber-mean residual square against the explicit fixed-right Markov
kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_aemeasurable_vacuum
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    AEMeasurable
      (fun C =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) := by
  classical
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
  let kappa :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
      H N hN beta hbeta
  letI : IsMarkovKernel kappa := by
    simpa [kappa] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_isMarkovKernel
        H N hN beta hbeta
  letI : IsSFiniteKernel kappa := by
    infer_instance
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
    exact
      ENNReal.continuous_ofReal.measurable.comp
        (hResidual.measurable.pow_const 2)
  have hSectionMeasurable :
      Measurable
        (fun C =>
          ∫⁻ A, Phi (C, A) ∂kappa C) := by
    exact hPhi.lintegral_kernel_prod_right'
  have hCanonical :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_residual_ae_eq_diagonalRemoteKernelSectionFluctuation_vacuum_kernelSection
      H N hN beta hbeta target target F hF
  have hEq :
      (fun C =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F) =ᵐ[
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta]
      (fun C => ∫⁻ A, Phi (C, A) ∂kappa C) := by
    filter_upwards [hCanonical] with C hC
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_apply
        H N hN beta hbeta C]
    apply lintegral_congr_ae
    filter_upwards [hC] with A hA
    let rightF :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
      fun D => F (C, D)
    have hRightStrong : StronglyMeasurable rightF :=
      hF.comp_measurable (measurable_const.prodMk measurable_id)
    have hRemote :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_diagonal_eq_value_sub_kernelSectionSpatialLinkIntegral
        H N hN beta hbeta C A target target rightF hRightStrong
    have hCanonicalAt :
        F (C, A) - center (outer (C, A)) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta C target target target
            (C target) (C target) rightF A := by
      simpa [center, outer, rightF] using hA
    have hResidualEq :
        F (C, A) -
            ∫ g,
              F (C, Function.update A target g)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta C A target =
          F (C, A) - center (outer (C, A)) := by
      calc
        F (C, A) -
            ∫ g,
              F (C, Function.update A target g)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
                H N hN beta hbeta C A target =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
            H N hN beta hbeta C target target target
            (C target) (C target) rightF A := by
              simpa [rightF] using hRemote.symm
        _ = F (C, A) - center (outer (C, A)) :=
          hCanonicalAt.symm
    simpa [Phi] using
      congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) hResidualEq
  exact hSectionMeasurable.aemeasurable.congr hEq.symm

/-- The outer vacuum lower integral commutes exactly with the finite target
residual-energy sum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedTargetKernelSectionResidualEnergySum_vacuum_lintegral_eq_sum_canonicalFiberVarianceFunctional
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (∫⁻ C,
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target (F target)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta target (F target) := by
  classical
  rw [
    lintegral_finset_sum'
      (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (f := fun target C =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target (F target))
      (fun target _ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_aemeasurable_vacuum
          H N hN beta hbeta target (F target) (hF target))]
  apply Finset.sum_congr rfl
  intro target htarget
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
      H N hN beta hbeta target
      (F target) (hF target) (bound target) (hbound target)

/-- Global link-indexed response-amplitude energy is bounded by the sum of the
genuine canonical target fiber variances with the volume-independent response
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_canonicalFiberVarianceFunctional_sum
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (∫⁻ C,
      ENNReal.ofReal
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
              H N hN beta hbeta C distinguishedSource
              (F target) (hF target) (bound target) (hbound target)
              source target) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
            H N hN beta hbeta target (F target) := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_targetResidualEnergySum_lintegral
      N hN s hs beta hbeta hcut H distinguishedSource
      F hF bound hbound
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedTargetKernelSectionResidualEnergySum_vacuum_lintegral_eq_sum_canonicalFiberVarianceFunctional
      H N hN beta hbeta F hF bound hbound] at hBase
  exact hBase

/-- Coefficient-one genuine-CondExp form of the global response-amplitude
energy bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_condExpL2ResidualNormSq_sum
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (∫⁻ C,
      ENNReal.ofReal
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
              H N hN beta hbeta C distinguishedSource
              (F target) (hF target) (bound target) (hbound target)
              source target) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta (F target) (hF target)
                  (bound target) (hbound target) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                  H N hN beta hbeta target
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta (F target) (hF target)
                    (bound target) (hbound target))‖ ^ 2) := by
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_canonicalFiberVarianceFunctional_sum
      N hN s hs beta hbeta hcut H distinguishedSource
      F hF bound hbound
  have hVariance :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta target (F target)) ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta (F target) (hF target)
                  (bound target) (hbound target) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                  H N hN beta hbeta target
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta (F target) (hF target)
                    (bound target) (hbound target))‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro target htarget
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
        H N hN beta hbeta target
        (F target) (hF target) (bound target) (hbound target)
  exact hResponse.trans
    (mul_le_mul_left'
      hVariance
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s beta))

end

end MGAP4D.MathlibAnalytic
