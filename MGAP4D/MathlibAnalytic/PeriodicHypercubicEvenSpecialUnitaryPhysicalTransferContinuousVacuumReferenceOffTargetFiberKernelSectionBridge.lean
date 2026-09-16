import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionOneSlabFiberBaseInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffTargetHarnack
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance referenceOffTargetFiberKernelSectionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceOffTargetFiberKernelSectionSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceOffTargetFiberKernelSectionSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceOffTargetFiberKernelSectionSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceOffTargetFiberKernelSectionSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Restrict the canonical positive reference weight
`Omega * targetLocalFactor * K(-, B[source <- k])` to one left spatial-link
fiber and convert it to an `ENNReal` Haar weight.

This is only a pointwise fiber weight.  No regular-conditional interpretation
is asserted. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
      H N hN beta hbeta B target source k g₂
      (Function.update A backgroundFiber g))

/-- Normalize one fiber of the canonical reference weight against compact Haar.
This remains a named normalized fiber law rather than an RCD claim. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
      H N hN beta hbeta B target source k g₂ A backgroundFiber)

/-- On a left fiber different from the distinguished target, the target-local
factor in the reference weight is constant in the fiber variable.  Hence the
reference fiber weight is exactly the complete fixed-right kernel-section
weight for `B[source <- k]`, multiplied by one positive finite constant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight_eq_kernelSection_mul_const_of_ne_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hBackgroundTarget : backgroundFiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
        H N hN beta hbeta B target source k g₂ A backgroundFiber g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkENNRealWeight
          H N hN beta hbeta (Function.update B source k) A backgroundFiber g *
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂) := by
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
      H N beta A B target backgroundFiber g g₂ hBackgroundTarget
  have hReal :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂
          (Function.update A backgroundFiber g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
            H N hN beta hbeta (Function.update B source k) A backgroundFiber g *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂ := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    rw [hLocal]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
    ring
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
  rw [hReal]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkENNRealWeight
  rw [ENNReal.ofReal_mul
    (le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkWeight_pos
        H N hN beta hbeta (Function.update B source k) A backgroundFiber g))]

/-- Fiber normalization removes the distinguished target-local factor exactly.
Thus every off-target one-link fiber of the covariance reference law is the
complete fixed-right kernel-section one-link law with right boundary
`B[source <- k]`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure_eq_kernelSection_of_ne_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hBackgroundTarget : backgroundFiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
        H N hN beta hbeta B target source k g₂ A backgroundFiber =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A backgroundFiber := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let wSection :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkENNRealWeight
      H N hN beta hbeta (Function.update B source k) A backgroundFiber
  let c : ℝ≥0∞ := ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A B target g₂)
  have hcPos : 0 < c := by
    exact ENNReal.ofReal_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta A B target g₂)
  have hcZero : c ≠ 0 := ne_of_gt hcPos
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hWeight :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
          H N hN beta hbeta B target source k g₂ A backgroundFiber =
        fun g => wSection g * c := by
    funext g
    simpa [wSection, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight_eq_kernelSection_mul_const_of_ne_target
        H N hN beta hbeta B target source backgroundFiber hBackgroundTarget k g₂ A g)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
  change
    doobWeightedMeasure μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberENNRealWeight
          H N hN beta hbeta B target source k g₂ A backgroundFiber) =
      doobWeightedMeasure μ wSection
  rw [hWeight]
  exact doobWeightedMeasure_mul_const_eq μ wSection c hcZero hcTop

/-- Equivalent local-section presentation of the same off-target reference
fiber law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure_eq_kernelSectionLocal_of_ne_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hBackgroundTarget : backgroundFiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
        H N hN beta hbeta B target source k g₂ A backgroundFiber =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalNormalizedMeasure
        H N hN beta hbeta (Function.update B source k) A backgroundFiber := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure_eq_kernelSection_of_ne_target
      H N hN beta hbeta B target source backgroundFiber hBackgroundTarget k g₂ A]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure_eq_local
      H N hN beta hbeta (Function.update B source k) A backgroundFiber

/-- Combining the off-target cancellation with the canonical raw/vacuum bridge,
every off-target fiber of the reference weight is exactly a continuous-vacuum
Doob reweighting of the raw one-slab local Boltzmann law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure_eq_raw_vacuum_doob_of_ne_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hBackgroundTarget : backgroundFiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure
        H N hN beta hbeta B target source k g₂ A backgroundFiber =
      doobWeightedMeasure
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkMeasure
          H N beta (Function.update B source k) A backgroundFiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkFiberWeight
          H N hN beta hbeta A backgroundFiber) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSpatialLinkFiberNormalizedMeasure_eq_kernelSectionLocal_of_ne_target
      H N hN beta hbeta B target source backgroundFiber hBackgroundTarget k g₂ A]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkLocalNormalizedMeasure_eq_raw_vacuum_doob
      H N hN beta hbeta (Function.update B source k) A backgroundFiber).symm

end

end MathlibAnalytic
end MGAP4D
