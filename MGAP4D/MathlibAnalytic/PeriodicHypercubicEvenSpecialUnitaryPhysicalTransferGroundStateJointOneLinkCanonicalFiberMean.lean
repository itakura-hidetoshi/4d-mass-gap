import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitContextCoordinateEquiv
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-!
# Canonical measurable one-link fiber mean for the genuine ground-state joint law

The historical one-link split disintegration already proves existence of a
Markov kernel whose fibers agree almost everywhere with the genuine normalized
target-link conditional laws.  Until now that kernel has been chosen afresh in
each theorem.

This file fixes one integrand-independent choice for each target link and uses
it to define the canonical bounded-concrete fiber mean

  m_F(left, retained)
    = ∫ targetCfg, F(left, reconstruct(targetCfg, retained)) dκ(left,retained).

The chosen kernel is Markov, agrees almost everywhere with the existing genuine
split normalized fiber law, and the resulting fiber mean is strongly
measurable in the outer context.

No conditional-expectation claim is made yet; that is the next unit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance groundStateJointCanonicalFiberMeanSpecialUnitaryTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointCanonicalFiberMeanSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointCanonicalFiberMeanSpecialUnitarySecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointCanonicalFiberMeanSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointCanonicalFiberMeanSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointCanonicalFiberMeanSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One fixed integrand-independent Markov kernel representing the genuine
ground-state target-link conditional laws. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Kernel
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)))
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  Classical.choose
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_exists_markovKernel
      H N hN beta hbeta target)

/-- The canonical chosen target-fiber kernel is Markov. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_isMarkovKernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
        H N hN beta hbeta target) :=
  (Classical.choose_spec
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_exists_markovKernel
      H N hN beta hbeta target)).1

/-- The canonical chosen kernel agrees almost everywhere with the literal
historical normalized split target fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_ae_eq_normalizedFiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ ctx ∂
        ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
          H N hN beta hbeta target ctx =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
          H N hN beta hbeta ctx.1 target ctx.2 :=
  (Classical.choose_spec
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_exists_markovKernel
      H N hN beta hbeta target)).2

/-- Canonical genuine one-link fiber mean of one concrete joint observable. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (ctx :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ))) : ℝ :=
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  ∫ targetCfg,
    F (coord (ctx, targetCfg))
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target ctx

/-- The canonical genuine fiber mean is strongly measurable in the outer
context whenever the concrete joint observable is strongly measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_stronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
        H N hN beta hbeta target F) := by
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_isMarkovKernel
      H N hN beta hbeta target
  have hJoint :
      StronglyMeasurable
        (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
                Matrix.specialUnitaryGroup (Fin N) ℂ))) ×
            (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          F (coord z)) :=
    hF.comp_measurable coord.measurable
  have hMean :
      StronglyMeasurable
        (fun ctx :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ)) =>
          ∫ targetCfg, F (coord (ctx, targetCfg)) ∂κ ctx) :=
    hJoint.integral_kernel_prod_right'
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean,
    κ, coord] using hMean

end

end MathlibAnalytic
end MGAP4D
