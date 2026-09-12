import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkJointVarianceTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumGroundStateContextVarianceTransferSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumGroundStateContextVarianceTransferSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumGroundStateContextVarianceTransferSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumGroundStateContextVarianceTransferSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumGroundStateContextVarianceTransferSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumGroundStateContextVarianceTransferSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance continuousVacuumGroundStateContextVarianceTransferTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance continuousVacuumGroundStateContextVarianceTransferTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- Pointwise transport lemma behind the context-dependent a.e. theorem.
Once a concrete outer context is known to satisfy the canonical map equality
and the literal split target fiber is known to be a probability measure, the
sharp direct `exp (-16 * beta)` variance estimate transfers with no additional
loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_evariance_lower_bound_of_map_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hmap :
      Measure.map
          (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta left
          (periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
            H N target retained) target)
    (hprob : IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
        H N hN beta hbeta left target retained)) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        evariance X
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
      evariance
        (fun targetCfg =>
          X (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta left target retained) := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
      H N hN beta hbeta left target retained
  let right := periodicHypercubicEvenSpecialUnitarySpatialSliceRightFromOffTarget
    H N target retained
  let νDirect :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
      H N hN beta hbeta left right target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using hprob
  have heval : MeasurePreserving eval ν νDirect := by
    refine ⟨eval.measurable, ?_⟩
    simpa [ν, νDirect, right, eval] using hmap
  have hXDirect : MemLp X 2 νDirect := by
    simpa [νDirect, right] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_memLp_two
        H N hN beta hbeta left right target X hX
  have hXActual : MemLp (fun targetCfg => X (eval targetCfg)) 2 ν :=
    hXDirect.comp_measurePreserving heval
  have hCenteredMap : ∀ c : ℝ,
      doobCenteredSquaredResidual νDirect X c =
        doobCenteredSquaredResidual ν (fun targetCfg => X (eval targetCfg)) c := by
    intro c
    unfold doobCenteredSquaredResidual
    symm
    simpa using
      heval.lintegral_comp_emb eval.measurableEmbedding
        (fun g => ENNReal.ofReal ((X g - c) ^ 2))
  have hBestMap :
      doobBestConstantSquaredResidual νDirect X =
        doobBestConstantSquaredResidual ν (fun targetCfg => X (eval targetCfg)) := by
    have hfun :
        (fun c : ℝ => doobCenteredSquaredResidual νDirect X c) =
          (fun c : ℝ =>
            doobCenteredSquaredResidual ν (fun targetCfg => X (eval targetCfg)) c) := by
      funext c
      exact hCenteredMap c
    simpa [doobBestConstantSquaredResidual] using
      congrArg (fun F : ℝ → ℝ≥0∞ => ⨅ c, F c) hfun
  have hVarianceMap :
      evariance X νDirect =
        evariance (fun targetCfg => X (eval targetCfg)) ν := by
    calc
      evariance X νDirect = doobBestConstantSquaredResidual νDirect X := by
        rw [doobBestConstantSquaredResidual_eq_evariance νDirect X hXDirect]
      _ = doobBestConstantSquaredResidual ν (fun targetCfg => X (eval targetCfg)) :=
        hBestMap
      _ = evariance (fun targetCfg => X (eval targetCfg)) ν :=
        doobBestConstantSquaredResidual_eq_evariance ν _ hXActual
  calc
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        evariance X
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
      evariance X νDirect := by
        simpa [νDirect, right] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_evariance_lower_bound
            H N hN beta hbeta left right target X hX
    _ = evariance (fun targetCfg => X (eval targetCfg)) ν := hVarianceMap

/-- Context-dependent sharp actual-fiber variance transfer.  This is the form
needed for a genuine joint observable: the one-link test function may vary with
the complete left boundary and with every retained off-target coordinate.
Only an a.e. `L²(Haar)` hypothesis is imposed on those one-link sections.

The exceptional outer contexts remain explicit and the coefficient is still
exactly `exp (-16 * beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_context_evariance_lower_bound_ae
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
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
            evariance (X left retained)
              (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
          evariance
            (fun targetCfg =>
              X left retained
                (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained) := by
  have hmap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
      H N hN beta hbeta target
  have hprob :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_isProbabilityMeasure
      H N hN beta hbeta target
  filter_upwards [hX, hmap, hprob] with left hXLeft hmapLeft hprobLeft
  filter_upwards [hXLeft, hmapLeft, hprobLeft] with retained hX' hmap' hprob'
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_evariance_lower_bound_of_map_eq
      H N hN beta hbeta target left retained (X left retained) hX' hmap' hprob'

end

end MathlibAnalytic
end MGAP4D
