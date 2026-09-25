import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMarkovIdentity
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance
import Mathlib.Tactic

/-!
# Variance minimality of the canonical genuine one-link fiber mean

PR #4750 fixes the canonical genuine split target-link Markov kernel and its
fiber mean.  PR #4751 proves that the same fixed kernel realizes the exact
split Fubini identity for every nonnegative measurable integrand.

This file records the fiberwise Hilbert/probability fact needed for the local
profile bridge:

* the squared residual around the canonical fiber mean is exactly Mathlib's
  extended variance;
* for a bounded strongly measurable concrete observable, that residual is no
  larger than the squared residual around any other constant center.

No outer integration or global conditional-expectation statement is made here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointCanonicalFiberVarianceSpecialUnitaryTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointCanonicalFiberVarianceSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointCanonicalFiberVarianceSpecialUnitarySecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointCanonicalFiberVarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointCanonicalFiberVarianceSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointCanonicalFiberVarianceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The canonical genuine one-link fiber mean is exactly the variance-minimizing
constant appearing in Mathlib's extended variance formula. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_centeredSquaredResidual_eq_evariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
          H N hN beta hbeta target ctx)
        (fun targetCfg =>
          F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
              H N target (ctx, targetCfg)))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
          H N hN beta hbeta target F ctx) =
      evariance
        (fun targetCfg =>
          F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
              H N target (ctx, targetCfg)))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
          H N hN beta hbeta target ctx) := by
  rw [evariance_eq_lintegral_ofReal]
  rfl

/-- For bounded concrete observables, the canonical fiber-mean residual is no
larger than the residual around any other scalar center. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_centeredSquaredResidual_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (ctx :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ))
    (c : ℝ) :
    doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
          H N hN beta hbeta target ctx)
        (fun targetCfg =>
          F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
              H N target (ctx, targetCfg)))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
          H N hN beta hbeta target F ctx) ≤
      doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
          H N hN beta hbeta target ctx)
        (fun targetCfg =>
          F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
              H N target (ctx, targetCfg)))
        c := by
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  let X := fun targetCfg => F (coord (ctx, targetCfg))
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_isMarkovKernel
      H N hN beta hbeta target
  have hXStrong : StronglyMeasurable X := by
    exact hF.comp_measurable
      (coord.measurable.comp (measurable_const.prodMk measurable_id))
  have hXLp : MemLp X 2 (κ ctx) := by
    apply MemLp.of_bound hXStrong.aestronglyMeasurable bound
    exact Filter.Eventually.of_forall fun targetCfg =>
      hbound (coord (ctx, targetCfg))
  calc
    doobCenteredSquaredResidual (κ ctx) X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
          H N hN beta hbeta target F ctx) =
      evariance X (κ ctx) := by
        simpa [κ, coord, X] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_centeredSquaredResidual_eq_evariance
            H N hN beta hbeta target F ctx
    _ ≤ doobCenteredSquaredResidual (κ ctx) X c :=
      evariance_le_doobCenteredSquaredResidual (κ ctx) X hXLp c
    _ =
      doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
          H N hN beta hbeta target ctx)
        (fun targetCfg =>
          F
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
              H N target (ctx, targetCfg)))
        c := by
      rfl

end

end MathlibAnalytic
end MGAP4D
