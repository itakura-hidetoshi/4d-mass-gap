import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointKernelSectionMeasureDisintegration
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkAEFiberCompatibility
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionLeftFiberNormalizedMeasure
import Mathlib.Tactic

/-!
# Kernel-section / genuine one-link fiber bridge

The whole-configuration disintegration in PR #4746 identifies the genuine
ground-state joint law with the physical vacuum outer law and the explicit
fixed-right kernel-section Markov kernel.

To connect the local-mean fluctuation from PR #4738 to the pre-existing genuine
joint one-link conditional-expectation residual, the one-link law inside each
kernel section must be identified with the genuine ground-state one-link fiber
law.

For fixed retained boundary `C`, base sampled configuration `A`, and target
link, the complete continuous-vacuum direct one-link weight differs from the
kernel-section local one-link weight only by the positive finite
fiber-independent constant

  lambda^{-1} * Omega_cont(C) * K(C,A).

Hence normalization removes this constant exactly.  Combining the resulting
pointwise measure identity with the existing a.e. compatibility of the
historical joint split fiber gives the desired bridge without exchanging
source/target indices and without restricting an arbitrary L2 representative
to a pointwise fiber.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance groundStateKernelSectionGenuineOneLinkFiberBridgeTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateKernelSectionGenuineOneLinkFiberBridgeCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateKernelSectionGenuineOneLinkFiberBridgeSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateKernelSectionGenuineOneLinkFiberBridgeMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateKernelSectionGenuineOneLinkFiberBridgeBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateKernelSectionGenuineOneLinkFiberBridgeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The complete continuous-vacuum direct one-link real weight is the
kernel-section local one-link weight times one positive factor independent of
the target value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_eq_kernelSectionLocalWeight_mul_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
        H N hN beta hbeta C A target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
          H N hN beta hbeta C A target g *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖⁻¹ *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta C *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta C A)) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
      H N beta C A target g]
  ring

/-- ENNReal form of the same factorization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_eq_kernelSectionLocalENNRealWeight_mul_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta C A target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalENNRealWeight
          H N hN beta hbeta C A target g *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                H N hN beta hbeta‖⁻¹ *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta C *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta C A)) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeightReal_eq_kernelSectionLocalWeight_mul_const
      H N hN beta hbeta C A target g]
  rw [ENNReal.ofReal_mul
    (le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight_pos
        H N hN beta hbeta C A target g))]
  rfl

/-- Fiberwise normalization removes the positive finite constant exactly.
Thus the one-link law inside a fixed-right kernel section is the genuine
continuous-vacuum direct ground-state one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_eq_continuousVacuumDirect
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta C A target := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let wLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalENNRealWeight
      H N hN beta hbeta C A target
  let wDirect :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta C A target
  let c : ℝ≥0∞ :=
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta C *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta C A))
  have hlambda :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have homega :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta C
  have hkernel :
      0 <
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta C A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta C A
  have hcPos : 0 < c := by
    exact ENNReal.ofReal_pos.mpr
      (mul_pos (inv_pos.mpr hlambda) (mul_pos homega hkernel))
  have hcZero : c ≠ 0 := ne_of_gt hcPos
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hScale : wDirect = fun g => wLocal g * c := by
    funext g
    simpa [wDirect, wLocal, c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_eq_kernelSectionLocalENNRealWeight_mul_const
        H N hN beta hbeta C A target g
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_eq_local
      H N hN beta hbeta C A target]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalNormalizedMeasure
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
  change doobWeightedMeasure μ wLocal = doobWeightedMeasure μ wDirect
  rw [hScale]
  exact (doobWeightedMeasure_mul_const_eq μ wLocal c hcZero hcTop).symm

/-- The historical genuine-joint split target fiber, after passing to the
literal target-group coordinate, agrees almost everywhere with the
kernel-section one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_kernelSectionContinuousSpatialLinkNormalizedMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        Measure.map
            (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta left
            (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
              H N target retained) target := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
      H N hN beta hbeta target] with left hleft
  filter_upwards [hleft] with retained hretained
  calc
    Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta left target retained) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
          H N target retained) target := hretained
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta left
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
          H N target retained) target :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_eq_continuousVacuumDirect
        H N hN beta hbeta left
        (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
          H N target retained) target).symm

end

end MathlibAnalytic
end MGAP4D
