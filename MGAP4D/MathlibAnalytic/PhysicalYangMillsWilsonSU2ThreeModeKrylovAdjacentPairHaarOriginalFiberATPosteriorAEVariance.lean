import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiberATPosteriorSpecialization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectNormalizedFiberBridge
import Mathlib.Tactic

/-!
# P4-Q2-AW: the ORIGINAL ground-state conditional fiber satisfies AT's
# volume-independent genuine one-link Wilson–Perron variance lower bound

AW's generic normalization and literal Wilson specialization prove the
canonical *continuous physical Wilson joint-density normalized right
one-link fiber* equals the genuine AS Wilson raw conditional tilted by
the actual continuous physical top vacuum (AT).

AV proves for Haar-a.e. left/off-target context that the EXACT old
physical ground-state normalized singleton target-link fiber equals
this canonical continuous fiber as a measure.

Here we push the AV target singleton to its DIRECT SU(N) link via the
actual Haar measure-preserving singleton evaluation, with NO fictitious
coordinate equivalence, and deduce for Haar-a.e. context the exact AT
volume-independent e^(-32 beta) lower bound for the ORIGINAL ground
state conditional law.

No claim at exceptional context fibers, and no global physical Dirichlet
mass-gap estimate from this one-link posterior variance.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open ProbabilityTheory
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

local instance p4AWAEGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AWAECompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AWAESecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AWAEMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AWAEBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AWAELinks (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AWAETargetLinks (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- Push the ACTUAL continuous physical joint-density normalized target
fiber to a direct SU(N) link. The result equals the direct normalized
physical one-link joint density for EVERY continuous-vacuum context,
without any hypothesis on exceptional L² representatives. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure_map_targetEvaluation_eq_directContinuous
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta left target
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber
        H N hN beta hbeta left right target := by
  classical
  let muTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let muGroup := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let e := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ENNReal := fun g =>
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
        H N hN beta hbeta left right target g)
  have hevalEval : MeasurePreserving
      (Function.eval
        (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
      muTarget muGroup := by
    simpa [muTarget, muGroup] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target => muGroup)
        (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target))
  have heval : MeasurePreserving e muTarget muGroup := by
    have hFun :
        (e : (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) →
          Matrix.specialUnitaryGroup (Fin N) ℂ) =
        Function.eval
          (⟨target, rfl⟩ : PeriodicHypercubicEvenSpatialSliceTargetLink H target) := by
      funext targetCfg
      simp [e]
    rw [hFun]
    exact hevalEval
  have hWeight :
      (fun targetCfg =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity
          H N hN beta hbeta left target targetCfg
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right)) =
      (w ∘ e) := by
    funext targetCfg
    change ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
        H N hN beta hbeta
        (left,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target right))) =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkJointWeight
          H N hN beta hbeta left right target (e targetCfg))
    rw [periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update]
    rfl
  change Measure.map e
      (doobWeightedMeasure muTarget
        (fun targetCfg =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetDensity
            H N hN beta hbeta left target targetCfg
              (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right))) =
    doobWeightedMeasure muGroup w
  rw [hWeight]
  exact p4Q2AW_measureMap_doobWeightedMeasure e muTarget muGroup heval w

/-- For Haar-almost every real left boundary and retained off-target
spatial configuration, EVERY completion of the same off-target context
gives the AT continuous physical Wilson posterior after the ORIGINAL
normalized split target fiber is pushed to its genuine SU(N) link.
No exceptional fixed fiber is promoted to a pointwise claim. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabOriginalGroundStateSplitTargetFiber_ae_map_eq_ATPosterior
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ ctx ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
      ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = ctx.2 →
      Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
        H N hN beta hbeta ctx.1 right target := by
  have hAV :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_eq_continuous
      H N hN beta hbeta target
  filter_upwards [hAV] with ctx hctx
  intro right hOff
  calc
    Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2) =
      Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2) := by rw [hctx]
    _ = Measure.map
        (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target right)) := by
          rw [hOff]
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber
          H N hN beta hbeta ctx.1 right target :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRightJointSplitTargetNormalizedFiberMeasure_map_targetEvaluation_eq_directContinuous
        H N hN beta hbeta ctx.1 right target
    _ = periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw
          H N hN beta hbeta ctx.1 right target :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateRightLinkNormalizedFiber_eq_ATPosterior
        H N hN beta hbeta ctx.1 right target

/-- AW main result: the ACTUAL original ground-state right-boundary
conditional fiber satisfies the AT physical Wilson local variance
comparison against SU(N) Haar, with precisely e^(-32 beta) and NO
spatial-volume factor, for Haar-almost every left/off-target context.

The tested observable X must be L² for Haar and the literal AS raw
Wilson one-link law; this is the same explicit hypothesis as AT.
Nothing here asserts a volume-uniform global physical transfer gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabOriginalGroundStateSplitTargetFiber_ae_evariance_ge_Haar
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ ctx ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
      ∀ (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N),
        periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = ctx.2 →
      ∀ (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ),
        MemLp X 2 (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) →
        MemLp X 2 (periodicHypercubicEvenSpecialUnitaryRightTargetLocalConditionalHaarLaw
          H N beta ctx.1 right target) →
        ENNReal.ofReal (Real.exp (-32 * beta)) *
          evariance X (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
        evariance X
          (Measure.map
            (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta ctx.1 target ctx.2)) := by
  have hEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabOriginalGroundStateSplitTargetFiber_ae_map_eq_ATPosterior
      H N hN beta hbeta target
  filter_upwards [hEq] with ctx hctx
  intro right hoff X hHaar hRaw
  rw [hctx right hoff]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumOriginalWilsonPosteriorLaw_evariance_ge_Haar
      H N hN beta hbeta ctx.1 right target X hHaar hRaw

end
end MathlibAnalytic
end MGAP4D
