import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberVarianceCenteredResidualEq
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberVarianceCondExpResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointKernelSectionLIntegralDisintegration
import Mathlib.Tactic

/-!
# Canonical fiber variance in joint and kernel-section residual coordinates

PR #4755 identifies the canonical weighted fiber variance exactly with the
genuine centered-residual functional centered at the canonical fiber mean.
PR #4756 exposes the exact genuine-joint / vacuum-kernel-section Fubini
identity.

Combining those results gives two exact presentations of the same energy:

1. as a squared canonical-mean residual under the genuine joint law;
2. as the physical-vacuum average of the same squared residual under each
   literal normalized fixed-right kernel-section law.

The latter is the integration carrier needed to compare directly with the
diagonal section L2 norms from PRs #4748--#4749.

No new comparison constant, source/target exchange, or Poincare estimate is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique

/-- The canonical weighted fiber variance is exactly the squared residual from
its own canonical fiber mean, integrated under the genuine ground-state joint
law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_joint_canonicalFiberMean_residual_lintegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      ∫⁻ z,
        ENNReal.ofReal
          ((F z -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                H N hN beta hbeta target F
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target z)) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
      H N hN beta hbeta target F
  have hC : StronglyMeasurable C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_stronglyMeasurable
        H N hN beta hbeta target F hF
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
        H N hN beta hbeta target F C := by
      simpa [C] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_centeredResidual_canonicalFiberMean
          H N hN beta hbeta target F
    _ =
      ∫⁻ z,
        ENNReal.ofReal
          ((F z -
              C
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target z)) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional_eq_joint_lintegral
        H N hN beta hbeta target F hF C hC
    _ =
      ∫⁻ z,
        ENNReal.ofReal
          ((F z -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                H N hN beta hbeta target F
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target z)) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta := by
      rfl

/-- The same canonical fiber variance is exactly the physical-vacuum average
of the canonical-mean residual energy in each literal fixed-right
kernel-section law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_vacuum_kernelSection_canonicalFiberMean_residual_lintegral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      ∫⁻ C,
        (∫⁻ A,
          ENNReal.ofReal
            ((F (C, A) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                  H N hN beta hbeta target F
                  (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                    H N target (C, A))) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
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
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F =
      ∫⁻ z, Phi z
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta := by
      simpa [Phi, center, outer] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_joint_canonicalFiberMean_residual_lintegral
          H N hN beta hbeta target F hF
    _ =
      ∫⁻ C,
        (∫⁻ A, Phi (C, A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_lintegral_eq_vacuum_kernelSection
        H N hN beta hbeta Phi hPhi
    _ =
      ∫⁻ C,
        (∫⁻ A,
          ENNReal.ofReal
            ((F (C, A) -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                  H N hN beta hbeta target F
                  (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                    H N target (C, A))) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      rfl

/-- The vacuum/kernel-section canonical residual energy is bounded with
coefficient one by the genuine global one-link CondExpL2 residual norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLink_vacuum_kernelSection_canonicalFiberMean_residual_lintegral_le_condExpL2_residual_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      (∫⁻ A,
        ENNReal.ofReal
          ((F (C, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                H N hN beta hbeta target F
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target (C, A))) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  calc
    (∫⁻ C,
      (∫⁻ A,
        ENNReal.ofReal
          ((F (C, A) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
                H N hN beta hbeta target F
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target (C, A))) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_vacuum_kernelSection_canonicalFiberMean_residual_lintegral
          H N hN beta hbeta target F hF
    _ ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
        H N hN beta hbeta target F hF bound hbound

end

end MathlibAnalytic
end MGAP4D
