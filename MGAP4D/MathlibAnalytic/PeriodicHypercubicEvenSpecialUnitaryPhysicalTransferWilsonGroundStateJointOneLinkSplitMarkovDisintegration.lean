import MGAP4D.MathlibAnalytic.DoobWeightedMeasurableMarkovKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAENormalizedFiberProbability
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitProductFiberMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

local instance specialUnitaryGroupIsTopologicalGroupForSplitMarkovDisintegration (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance specialUnitaryGroupCompactSpaceForSplitMarkovDisintegration (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance specialUnitaryGroupSecondCountableTopologyForSplitMarkovDisintegration (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance specialUnitaryGroupMeasurableSpaceForSplitMarkovDisintegration (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance specialUnitaryGroupBorelSpaceForSplitMarkovDisintegration (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance periodicHypercubicEvenSpatialSliceLinkFintypeForSplitMarkovDisintegration
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForSplitMarkovDisintegration
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- The actual ground-state target/off-target split admits an everywhere-defined
Markov kernel on the canonical singleton-target configuration carrier, agreeing
for `(left, retained)` product-Haar almost every context with the literal
normalized split target fiber.

This is a measurable-kernel representative theorem only.  It does not identify
the kernel as a regular conditional distribution or as the Wilson one-link
conditional law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_exists_markovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∃ κ : Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ))
        (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ),
      IsMarkovKernel κ ∧
        ∀ᵐ ctx ∂
            ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
              (Measure.pi
                (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                  normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
          κ ctx =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta ctx.1 target ctx.2 := by
  classical
  let μLeft := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let w := fun
      (ctx : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ))
      (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
      H N hN beta hbeta ctx.1 target (targetCfg, ctx.2)
  have hw : AEMeasurable (Function.uncurry w) ((μLeft.prod μOff).prod μTarget) := by
    simpa [μLeft, μOff, μTarget, w] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_aemeasurable_contextTarget
        H N hN beta hbeta target)
  have hMass :
      ∀ᵐ ctx ∂(μLeft.prod μOff),
        0 < doobWeightMass μTarget (w ctx) ∧
          doobWeightMass μTarget (w ctx) < ∞ := by
    simpa [μLeft, μOff, μTarget, w] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetDoobWeightMass_ae_pos_lt_top_prod
        H N hN beta hbeta target)
  letI : IsProbabilityMeasure μLeft := by
    dsimp [μLeft]
    infer_instance
  letI : IsProbabilityMeasure μOff := by
    dsimp [μOff]
    infer_instance
  letI : IsProbabilityMeasure (μLeft.prod μOff) := by
    infer_instance
  have hμCtx : μLeft.prod μOff ≠ 0 := by
    intro hzero
    have huniv : (μLeft.prod μOff) Set.univ = 1 := measure_univ
    rw [hzero] at huniv
    simpa using huniv
  obtain ⟨κ, hκ, hκae⟩ :=
    exists_doobWeightedMarkovKernel_ae_eq
      (μLeft.prod μOff) μTarget w hw hμCtx hMass
  refine ⟨κ, hκ, ?_⟩
  simpa [μLeft, μOff, μTarget, w,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure]
    using hκae

/-- Exact global ground-state split normalization identity realized by one
measurable Markov kernel.  The kernel agrees almost everywhere with the literal
normalized singleton-target fibers, and the exact target-fiber mass remains
visible on the outer integral.

This is an exact weighted product-integral identity, not an RCD identification
and not a Wilson conditional-law theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_exists_markovKernel_lintegral_identity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) →
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞)
    (hF : AEMeasurable (Function.uncurry F)
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))))) :
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
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
                H N hN beta hbeta z.1.1 target (z.2, z.1.2) *
              F z.1 z.2
          ∂(((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
              (Measure.pi
                (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                  normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))).prod
            (Measure.pi
              (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
                normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))))) =
          ∫⁻ ctx,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta ctx.1 target ctx.2 *
              (∫⁻ targetCfg, F ctx targetCfg ∂κ ctx)
            ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
              (Measure.pi
                (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
                  normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  classical
  let μLeft := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let w := fun
      (ctx : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ))
      (targetCfg : PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
      H N hN beta hbeta ctx.1 target (targetCfg, ctx.2)
  have hw : AEMeasurable (Function.uncurry w) ((μLeft.prod μOff).prod μTarget) := by
    simpa [μLeft, μOff, μTarget, w] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_aemeasurable_contextTarget
        H N hN beta hbeta target)
  have hMass :
      ∀ᵐ ctx ∂(μLeft.prod μOff),
        0 < doobWeightMass μTarget (w ctx) ∧
          doobWeightMass μTarget (w ctx) < ∞ := by
    simpa [μLeft, μOff, μTarget, w] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetDoobWeightMass_ae_pos_lt_top_prod
        H N hN beta hbeta target)
  have hF' : AEMeasurable (Function.uncurry F) ((μLeft.prod μOff).prod μTarget) := by
    simpa [μLeft, μOff, μTarget] using hF
  letI : IsProbabilityMeasure μLeft := by
    dsimp [μLeft]
    infer_instance
  letI : IsProbabilityMeasure μOff := by
    dsimp [μOff]
    infer_instance
  letI : IsProbabilityMeasure (μLeft.prod μOff) := by
    infer_instance
  have hμCtx : μLeft.prod μOff ≠ 0 := by
    intro hzero
    have huniv : (μLeft.prod μOff) Set.univ = 1 := measure_univ
    rw [hzero] at huniv
    simpa using huniv
  obtain ⟨κ, hκ, hκae, hid⟩ :=
    exists_doobWeightedMarkovKernel_lintegral_identity
      (μLeft.prod μOff) μTarget w F hw hF' hμCtx hMass
  refine ⟨κ, hκ, ?_, ?_⟩
  · simpa [μLeft, μOff, μTarget, w,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure]
      using hκae
  · have hmassEq : ∀ ctx,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta ctx.1 target ctx.2 =
          doobWeightMass μTarget (w ctx) := by
      intro ctx
      simpa [μTarget, w] using
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass
          H N hN beta hbeta ctx.1 target ctx.2)
    simpa only [μLeft, μOff, μTarget, w, hmassEq] using hid

end

end MathlibAnalytic
end MGAP4D
