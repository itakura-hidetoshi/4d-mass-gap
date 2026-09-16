import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionOneSlabRawDoob
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance kernelSectionOneSlabRawContinuitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance kernelSectionOneSlabRawContinuitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance kernelSectionOneSlabRawContinuitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance kernelSectionOneSlabRawContinuitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance kernelSectionOneSlabRawContinuitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The exact one-slab right-target local Boltzmann factor is continuous in the
resampled link.  The proof uses `Continuous.comp₂` directly on the jointly
continuous kernel, avoiding the product-function definitional-equality path
that caused the earlier elaboration timeout. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous
    (H N : ℕ)
    (beta : ℝ)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta C A target g) := by
  let k0 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta C A
  have hk0 : k0 ≠ 0 := by
    exact ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta C A)
  have hUpdate : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => Function.update A target g) := by
    simpa [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A target)
  have hNum : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta C (Function.update A target g)) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).comp₂ continuous_const hUpdate
  have hEq :
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta C A target g) =
      (fun g =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta C (Function.update A target g) / k0) := by
    funext g
    apply (eq_div_iff hk0).2
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul
        H N beta C A target g).symm
  rw [hEq]
  exact hNum.div_const k0

/-- The ENNReal raw one-slab Haar weight is continuous. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight_continuous
    (H N : ℕ)
    (beta : ℝ)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight
        H N beta C A target) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight
  exact ENNReal.continuous_ofReal.comp
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous
      H N beta C A target)

/-- Consequently the raw one-slab Haar weight is a.e.-measurable against any
measure on the link group. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight_aemeasurable
    (H N : ℕ)
    (beta : ℝ)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (ν : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    AEMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight
        H N beta C A target) ν := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernelSectionRawSpatialLinkWeight_continuous
      H N beta C A target).measurable.aemeasurable

end

end MathlibAnalytic
end MGAP4D
