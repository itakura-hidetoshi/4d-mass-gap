import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkContextVarianceTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointOneLinkIntegratedVarianceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointOneLinkIntegratedVarianceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointOneLinkIntegratedVarianceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointOneLinkIntegratedVarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointOneLinkIntegratedVarianceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointOneLinkIntegratedVarianceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateJointOneLinkIntegratedVarianceTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance groundStateJointOneLinkIntegratedVarianceTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- The sharp context-dependent actual-fiber variance estimate survives exact
weighting by the genuine singleton-target fiber mass and iterated integration
over the complete left boundary and retained off-target right boundary.

No measurable representative of an arbitrary joint `L²` class is selected in
this theorem.  It is the integration bridge from the canonical a.e. fiberwise
variance theorem toward genuine joint `condExpL2` residual coercivity.  The
coefficient remains exactly `(ENNReal.ofReal (Real.exp (16 * beta)))⁻¹`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_context_evariance_weighted_lintegral_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
          MemLp (X left retained) 2
            (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    (∫⁻ left,
      ∫⁻ retained,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
              H N hN beta hbeta left target retained *
            ((ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
              evariance (X left retained)
                (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
          ∂(Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
      (∫⁻ left,
        ∫⁻ retained,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained *
              evariance
                (fun targetCfg =>
                  X left retained
                    (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
                  H N hN beta hbeta left target retained)
            ∂(Measure.pi
              (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  have hvar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_context_evariance_lower_bound_ae
      H N hN beta hbeta target X hX
  refine lintegral_mono_ae ?_
  filter_upwards [hvar] with left hleft
  refine lintegral_mono_ae ?_
  filter_upwards [hleft] with retained hretained
  exact mul_le_mul_left'
    hretained
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
      H N hN beta hbeta left target retained)

end

end MathlibAnalytic
end MGAP4D
