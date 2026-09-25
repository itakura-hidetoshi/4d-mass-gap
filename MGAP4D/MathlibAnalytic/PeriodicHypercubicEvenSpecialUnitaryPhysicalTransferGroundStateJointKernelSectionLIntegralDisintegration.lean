import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointKernelSectionMeasureDisintegration
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

/-!
# LIntegral form of the genuine joint/kernel-section disintegration

PR #4746 proves the integrand-independent measure identity

  mu_joint = mu_vacuum tensor_m kappa_section.

This file exposes the corresponding nonnegative measurable Fubini identity.
It is the direct integration interface needed to average the diagonal section
energies from PR #4749 over the physical vacuum law.

No new density algebra, comparison estimate, or source/target exchange is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

attribute [local instance]
  groundStateJointKernelSectionMeasureDisintegrationTopologicalGroup
  groundStateJointKernelSectionMeasureDisintegrationCompactSpace
  groundStateJointKernelSectionMeasureDisintegrationSecondCountable
  groundStateJointKernelSectionMeasureDisintegrationMeasurableSpace
  groundStateJointKernelSectionMeasureDisintegrationBorelSpace
  groundStateJointKernelSectionMeasureDisintegrationSpatialLinkFintype

/-- Integration under the genuine joint law is exactly vacuum averaging of
integration under the normalized fixed-right kernel-section law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_lintegral_eq_vacuum_kernelSection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    (∫⁻ z, Phi z
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) =
      ∫⁻ C,
        (∫⁻ A, Phi (C, A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
  letI :
      IsProbabilityMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
      H N hN beta hbeta
  letI :
      IsMarkovKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
          H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_isMarkovKernel
      H N hN beta hbeta
  letI :
      SFinite
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) := by
    infer_instance
  letI :
      IsSFiniteKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel
          H N hN beta hbeta) := by
    infer_instance
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_eq_vacuum_compProd_kernelSectionMarkovKernel
      H N hN beta hbeta]
  rw [Measure.lintegral_compProd hPhi]
  apply lintegral_congr
  intro C
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousMarkovKernel_apply
      H N hN beta hbeta C]

end

end MathlibAnalytic
end MGAP4D
