import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkAEFiberCompatibility
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAENormalizedFiberProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumGroundStateJointVarianceTransferSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumGroundStateJointVarianceTransferSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumGroundStateJointVarianceTransferSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumGroundStateJointVarianceTransferSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumGroundStateJointVarianceTransferSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumGroundStateJointVarianceTransferSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance continuousVacuumGroundStateJointVarianceTransferTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance continuousVacuumGroundStateJointVarianceTransferTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- The sharp fixed-center one-link residual transfers to the literal actual
split ground-state target fiber for almost every outer context.  The target
observable is pulled back only through the canonical singleton-coordinate
measurable equivalence, and the Harnack factor is paid exactly once. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_centeredSquaredResidual_lower_bound_ae
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (c : ℝ) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
            doobCenteredSquaredResidual
              (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X c ≤
          doobCenteredSquaredResidual
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained)
            (fun targetCfg =>
              X (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg)) c := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
      H N hN beta hbeta target] with left hleft
  filter_upwards [hleft] with retained hmap
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
  have heval : MeasurePreserving eval ν νDirect := by
    refine ⟨eval.measurable, ?_⟩
    simpa [ν, νDirect, right, eval] using hmap
  have hResidualMap :
      doobCenteredSquaredResidual νDirect X c =
        doobCenteredSquaredResidual ν (fun targetCfg => X (eval targetCfg)) c := by
    unfold doobCenteredSquaredResidual
    symm
    simpa using
      heval.lintegral_comp_emb eval.measurableEmbedding
        (fun g => ENNReal.ofReal ((X g - c) ^ 2))
  calc
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        doobCenteredSquaredResidual
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X c ≤
      doobCenteredSquaredResidual νDirect X c := by
        simpa [νDirect, right] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_centeredSquaredResidual_lower_bound
            H N hN beta hbeta left right target X c
    _ = doobCenteredSquaredResidual ν (fun targetCfg => X (eval targetCfg)) c :=
      hResidualMap

/-- The preceding transport is uniform in the center, hence it descends to the
best-constant residual without intersecting an uncountable family of outer
almost-everywhere statements. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_bestConstantSquaredResidual_lower_bound_ae
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
            doobBestConstantSquaredResidual
              (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X ≤
          doobBestConstantSquaredResidual
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained)
            (fun targetCfg =>
              X (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg)) := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
      H N hN beta hbeta target] with left hleft
  filter_upwards [hleft] with retained hmap
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
  have heval : MeasurePreserving eval ν νDirect := by
    refine ⟨eval.measurable, ?_⟩
    simpa [ν, νDirect, right, eval] using hmap
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
  calc
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        doobBestConstantSquaredResidual
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X ≤
      doobBestConstantSquaredResidual νDirect X := by
        simpa [νDirect, right] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_bestConstantSquaredResidual_lower_bound
            H N hN beta hbeta left right target X
    _ = doobBestConstantSquaredResidual ν (fun targetCfg => X (eval targetCfg)) :=
      hBestMap

/-- Sharp conditional-variance transfer to the actual split ground-state
one-link update.  For Haar-a.e. outer context the literal normalized target
fiber is a probability measure, and the singleton-coordinate pullback of every
Haar-`L²` observable retains the exact `exp (-16 * beta)` lower coefficient.

This remains a fiberwise statement on the actual joint split carrier.  It does
not identify the fiber as an RCD and does not evaluate any arbitrary `L²`
quotient representative pointwise. -/
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
            (fun targetCfg =>
              X (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained) := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_map_eq_continuousVacuumDirect
      H N hN beta hbeta target,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_isProbabilityMeasure
      H N hN beta hbeta target] with left hleftMap hleftProb
  filter_upwards [hleftMap, hleftProb] with retained hmap hprob
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

end

end MathlibAnalytic
end MGAP4D
