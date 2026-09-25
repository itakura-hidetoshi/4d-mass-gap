import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMean
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitMarkovDisintegration
import Mathlib.Tactic

/-!
# Canonical split-kernel integral identity

PR #4750 fixes one integrand-independent Markov kernel for each genuine
ground-state target-link split fiber.  The historical split Fubini theorem,
however, returns a fresh witness kernel for each integrand.

Both kernels agree almost everywhere with the same literal normalized split
fiber.  Therefore the witness-kernel inner integral may be replaced
outer-almost-everywhere by the canonical-kernel inner integral.

This file records the resulting exact split Fubini identity for the canonical
kernel.  No new estimate and no conditional-expectation claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

attribute [local instance]
  specialUnitaryGroupIsTopologicalGroupForSplitMarkovDisintegration
  specialUnitaryGroupCompactSpaceForSplitMarkovDisintegration
  specialUnitaryGroupSecondCountableTopologyForSplitMarkovDisintegration
  specialUnitaryGroupMeasurableSpaceForSplitMarkovDisintegration
  specialUnitaryGroupBorelSpaceForSplitMarkovDisintegration
  periodicHypercubicEvenSpatialSliceLinkFintypeForSplitMarkovDisintegration
  periodicHypercubicEvenSpatialSliceTargetLinkFintypeForSplitMarkovDisintegration

/-- The fixed canonical split target-link Markov kernel satisfies the exact
historical split Fubini identity for every nonnegative measurable integrand. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_lintegral_identity
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
          (∫⁻ targetCfg, F ctx targetCfg
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
              H N hN beta hbeta target ctx)
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  let μCtx :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
  obtain ⟨κ, _hκ, hκae, hid⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_exists_markovKernel_lintegral_identity
      H N hN beta hbeta target F hF
  have hcanon :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_ae_eq_normalizedFiber
      H N hN beta hbeta target
  have hKernel :
      κ =ᵐ[μCtx]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
          H N hN beta hbeta target := by
    filter_upwards [hκae, hcanon] with ctx hκctx hcanonctx
    exact hκctx.trans hcanonctx.symm
  calc
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
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := hid
    _ =
      ∫⁻ ctx,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta ctx.1 target ctx.2 *
          (∫⁻ targetCfg, F ctx targetCfg
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
              H N hN beta hbeta target ctx)
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
      apply lintegral_congr_ae
      filter_upwards [hKernel] with ctx hctx
      rw [hctx]

end

end MathlibAnalytic
end MGAP4D
