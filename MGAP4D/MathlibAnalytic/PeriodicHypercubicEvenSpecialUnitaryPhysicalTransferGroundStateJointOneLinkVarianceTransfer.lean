import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkAEFiberCompatibility
import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointOneLinkVarianceTransferSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointOneLinkVarianceTransferSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointOneLinkVarianceTransferSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointOneLinkVarianceTransferSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointOneLinkVarianceTransferSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The sharp `exp (-16 * beta)` one-link variance lower bound transfers,
almost everywhere in the genuine ground-state joint outer context, from the
canonical continuous-vacuum direct `SU(N)` fiber to the actual normalized
singleton-target split fiber.

The observable on the split fiber is obtained only by evaluating its unique
target coordinate.  The proof uses equality of pushforward measures from the
a.e. fiber-compatibility theorem and `IdentDistrib`; no pointwise choice of the
legacy `L²` vacuum representative is made. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_evariance_lower_bound_ae
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
            evariance X
              (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
          evariance
            (X ∘
              periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained) := by
  classical
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
      H N hN beta hbeta target] with left hleft
  filter_upwards [hleft] with retained hmap
  let right := periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
    H N target retained
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
      H N hN beta hbeta left target retained
  let μDirect :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
      H N hN beta hbeta left right target
  have hmap' : Measure.map eval ν = μDirect := by
    simpa [eval, ν, μDirect, right] using hmap
  have hXDirect : MemLp X 2 μDirect := by
    simpa [μDirect, right] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_memLp_two
        H N hN beta hbeta left right target X hX
  have hIdentEval :
      IdentDistrib eval id ν μDirect := by
    refine ⟨eval.measurable.aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa [hmap'] using hmap'
  have hXMap : AEMeasurable X (Measure.map eval ν) := by
    rw [hmap']
    exact hXDirect.aestronglyMeasurable.aemeasurable
  have hIdentX : IdentDistrib (X ∘ eval) X ν μDirect := by
    have h := hIdentEval.comp_of_aemeasurable hXMap
    simpa only [Function.comp_id] using h
  have hVariance :
      evariance (X ∘ eval) ν = evariance X μDirect :=
    hIdentX.evariance_eq
  have hSharp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_evariance_lower_bound
      H N hN beta hbeta left right target X hX
  rw [hVariance]
  simpa [μDirect, right] using hSharp

end

end MathlibAnalytic
end MGAP4D
