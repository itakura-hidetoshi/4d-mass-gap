import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitContextCoordinateEquiv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

local instance specialUnitaryGroupIsTopologicalGroupForOriginalCoordinateMarkovIdentity (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance specialUnitaryGroupCompactSpaceForOriginalCoordinateMarkovIdentity (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance specialUnitaryGroupSecondCountableTopologyForOriginalCoordinateMarkovIdentity (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance specialUnitaryGroupMeasurableSpaceForOriginalCoordinateMarkovIdentity (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance specialUnitaryGroupBorelSpaceForOriginalCoordinateMarkovIdentity (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance periodicHypercubicEvenSpatialSliceLinkFintypeForOriginalCoordinateMarkovIdentity
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForOriginalCoordinateMarkovIdentity
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- Exact global ground-state one-link Markov identity with the left-hand side
written back in the original complete-right-boundary coordinates.

The observable `G` lives on the genuine `(left, complete-right)` configuration
space.  On the right-hand side it is pulled back only through the already
canonical target/off-target measurable equivalence.  The kernel remains on the
singleton-target configuration carrier and agrees product-Haar a.e. with the
literal normalized split target fiber.

This theorem is a coordinate transport of the split weighted-product identity.
It makes no regular-conditional-distribution or Wilson conditional-law
identification. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointTarget_exists_markovKernel_original_lintegral_identity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (G :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hG : AEMeasurable (Function.uncurry G)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) :
    ∃ κ : Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ))
        (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ),
      IsMarkovKernel κ ∧
        (∀ᵐ ctx ∂
            ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
              (Measure.pi
                (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                  normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
          κ ctx =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta ctx.1 target ctx.2) ∧
        (∫⁻ z,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
                H N hN beta hbeta z.1 z.2 *
              G z.1 z.2
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
          ∫⁻ ctx,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta ctx.1 target ctx.2 *
              (∫⁻ targetCfg,
                G ctx.1
                  ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                    (targetCfg, ctx.2))
                ∂κ ctx)
            ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
              (Measure.pi
                (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                  normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  let F := fun
      (ctx : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ))
      (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    G ctx.1 (split.symm (targetCfg, ctx.2))
  have hcoord : MeasurePreserving coord ((μ.prod μOff).prod μTarget) (μ.prod μ) := by
    simpa [coord, μ, μOff, μTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
        H N target)
  have hG' : AEMeasurable (Function.uncurry G) (μ.prod μ) := by
    simpa [μ] using hG
  have hF : AEMeasurable (Function.uncurry F) ((μ.prod μOff).prod μTarget) := by
    have hcomp := hG'.comp_quasiMeasurePreserving hcoord.quasiMeasurePreserving
    simpa [F, coord, split, Function.comp_def] using hcomp
  obtain ⟨κ, hκ, hκae, hsplitIdentity⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_exists_markovKernel_lintegral_identity
      H N hN beta hbeta target F hF
  refine ⟨κ, hκ, hκae, ?_⟩
  have htransport :
      (∫⁻ z,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
              H N hN beta hbeta z.1.1 target (z.2, z.1.2) *
            F z.1 z.2
        ∂((μ.prod μOff).prod μTarget)) =
        ∫⁻ z,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
              H N hN beta hbeta z.1 z.2 *
            G z.1 z.2
          ∂(μ.prod μ) := by
    have h := hcoord.lintegral_comp_emb coord.measurableEmbedding
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
            H N hN beta hbeta z.1 z.2 *
          G z.1 z.2)
    simpa [coord, F, split,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity]
      using h
  calc
    (∫⁻ z,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
            H N hN beta hbeta z.1 z.2 *
          G z.1 z.2
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
      ∫⁻ z,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta z.1.1 target (z.2, z.1.2) *
          F z.1 z.2
        ∂((μ.prod μOff).prod μTarget) := by
          simpa [μ] using htransport.symm
    _ = ∫⁻ ctx,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
              H N hN beta hbeta ctx.1 target ctx.2 *
            (∫⁻ targetCfg,
              G ctx.1
                ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
                  (targetCfg, ctx.2))
              ∂κ ctx)
          ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
            (Measure.pi
              (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
          simpa [μ, μOff, μTarget, F, split] using hsplitIdentity

end

end MathlibAnalytic
end MGAP4D
