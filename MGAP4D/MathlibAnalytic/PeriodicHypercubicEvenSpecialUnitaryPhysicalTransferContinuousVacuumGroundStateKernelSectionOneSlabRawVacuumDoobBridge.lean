import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionOneSlabRawContinuity
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance kernelSectionRawVacuumDoobBridgeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance kernelSectionRawVacuumDoobBridgeSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance kernelSectionRawVacuumDoobBridgeSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance kernelSectionRawVacuumDoobBridgeSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance kernelSectionRawVacuumDoobBridgeSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The nonconstant fixed-right kernel-section one-link law is exactly the
continuous-vacuum Doob reweighting of the raw one-slab local Boltzmann law.

This is a measure-level normalized-weight identity only.  It does not identify
either measure with a regular conditional probability or a full 4D Wilson
Gibbs conditional. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalNormalizedMeasure_eq_raw_vacuum_doob
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta C A target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta A target) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalNormalizedMeasure
        H N hN beta hbeta C A target := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let r :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight
      H N beta C A target
  let v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
      H N hN beta hbeta A target
  let wLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalENNRealWeight
      H N hN beta hbeta C A target
  let m : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-8 * beta))
  let M : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  have hr : AEMeasurable r μ := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight_continuous
        H N beta C A target).measurable.aemeasurable
  have hv : AEMeasurable v μ := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight_continuous
        H N hN beta hbeta A target).measurable.aemeasurable
  have hm : 0 < m := by
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hM : M < ∞ := ENNReal.ofReal_lt_top
  have hLower : ∀ g, m ≤ r g := by
    intro g
    apply ENNReal.ofReal_le_ofReal
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
        H N hN beta hbeta C A target g
  have hUpper : ∀ g, r g ≤ M := by
    intro g
    apply ENNReal.ofReal_le_ofReal
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
        H N hN beta hbeta C A target g
  have hMassLower : m ≤ doobWeightMass μ r :=
    doobWeightMass_lower_bound μ r m hLower
  have hMassUpper : doobWeightMass μ r ≤ M :=
    doobWeightMass_upper_bound μ r M hUpper
  have hMassRZero : doobWeightMass μ r ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hm hMassLower)
  have hMassRTop : doobWeightMass μ r ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hMassUpper hM)
  have hCompose :
      doobWeightedMeasure (doobWeightedMeasure μ r) v =
        doobWeightedMeasure μ (fun g => r g * v g) :=
    doobWeightedMeasure_compose μ r v hr hv hMassRZero hMassRTop
  have hProduct : (fun g => r g * v g) = wLocal := by
    funext g
    have hFactor :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalWeight_ofReal_eq_vacuum_mul_raw
        H N hN beta hbeta C A target g
    simpa [r, v, wLocal,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalENNRealWeight,
      mul_comm] using hFactor.symm
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalNormalizedMeasure
  change doobWeightedMeasure (doobWeightedMeasure μ r) v =
    doobWeightedMeasure μ wLocal
  rw [hCompose, hProduct]

end

end MathlibAnalytic
end MGAP4D
