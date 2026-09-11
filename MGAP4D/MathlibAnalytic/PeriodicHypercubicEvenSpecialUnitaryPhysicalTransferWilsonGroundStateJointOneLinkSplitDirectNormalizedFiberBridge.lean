import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectFiberBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkNormalizedFiberMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Keep the singleton target subtype on the same explicit `Fintype`
presentation as the canonical split target-fiber layer. -/
local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForSplitDirectNormalizedFiber
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- The selected-link subtype is literally a singleton.  This local instance
keeps the carrier unchanged while making the evaluation equivalence available. -/
local instance periodicHypercubicEvenSpatialSliceTargetLinkUniqueForSplitDirectNormalizedFiber
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- Evaluation of the canonical singleton split target coordinate pushes the
normalized split ground-state target-fiber measure exactly to the already
constructed direct `SU(N)` normalized ground-state one-link fiber measure.

This is a pure coordinate/measure bridge.  It does not identify either side
with an RCD or with the raw Wilson one-link conditional law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_map_targetEvaluation_eq_directNormalizedFiberMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta left target
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target := by
  classical
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μGroup := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  have hevalEval :
      MeasurePreserving
        (Function.eval
          (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
        μTarget μGroup := by
    simpa [μTarget, μGroup] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target => μGroup)
        (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
  have heval : MeasurePreserving eval μTarget μGroup := by
    have hfun :
        (eval :
          (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =
        Function.eval
          (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target) := by
      funext targetCfg
      simp [eval]
    rw [hfun]
    exact hevalEval
  ext s hs
  rw [Measure.map_apply eval.measurable hs]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_apply
    H N hN beta hbeta left right target s hs]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
  rw [doobWeightedMeasure, withDensity_apply _ (hs.preimage eval.measurable)]
  unfold doobWeightedDensity
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass
    H N hN beta hbeta left target
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right)]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_offTargetRestriction_eq_directFiberMass
    H N hN beta hbeta left right target]
  change
    (∫⁻ targetCfg in eval ⁻¹' s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta left target
              (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
            H N hN beta hbeta left right target
      ∂μTarget) =
      ∫⁻ g in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
            H N hN beta hbeta left right target g /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
            H N hN beta hbeta left right target
        ∂μGroup
  calc
    (∫⁻ targetCfg in eval ⁻¹' s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta left target
              (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
            H N hN beta hbeta left right target
      ∂μTarget) =
      ∫⁻ targetCfg in eval ⁻¹' s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
            H N hN beta hbeta left right target (eval targetCfg) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
            H N hN beta hbeta left right target
        ∂μTarget := by
      apply lintegral_congr
      intro targetCfg
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_offTargetRestriction_eq_directFiberWeight
        H N hN beta hbeta left right target targetCfg]
    _ = ∫⁻ g in s,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
            H N hN beta hbeta left right target g /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
            H N hN beta hbeta left right target
        ∂μGroup := by
      exact
        heval.setLIntegral_comp_preimage_emb eval.measurableEmbedding
          (fun g =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
                H N hN beta hbeta left right target g /
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberMass
                H N hN beta hbeta left right target)
          s

end

end MathlibAnalytic
end MGAP4D
