import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalVarianceVacuumDiagonalSectionL2
import Mathlib.Tactic

/-!
# Canonical fiber-mean residual as a genuine joint L2 vector

The coefficient-one localPart energy bridge is now integrated: PR #4767
identifies the canonical genuine target-fiber variance with the physical-vacuum
average of the squared diagonal kernel-section L2 norms.

For the dependent response assembler we also need an actual normed vector, not
only its energy.  This file fixes the canonical centered residual

  F(z) - m_F(outer(z))

as a genuine vector in the ground-state joint L2 space.

Its squared L2 norm, after ENNReal.ofReal, is exactly the canonical fiber
variance.  Consequently it inherits the existing coefficient-one bound by the
genuine one-link CondExpL2 residual norm squared.

No response estimate, comparison loss, or Poincare input is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

/-- Concrete canonical residual centered by the fixed genuine split fiber mean. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  F z -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
      H N hN beta hbeta target F
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
        H N target z)

/-- The canonical fiber mean of a bounded concrete observable has the same
pointwise norm bound as the observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_norm_le_of_bounded
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (ctx :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
        H N hN beta hbeta target F ctx‖ ≤ bound := by
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  letI : IsMarkovKernel κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_isMarkovKernel
      H N hN beta hbeta target
  letI : IsProbabilityMeasure (κ ctx) := by
    infer_instance
  have h :=
    norm_integral_le_of_norm_le_const
      (μ := κ ctx)
      (C := bound)
      (f := fun targetCfg => F (coord (ctx, targetCfg)))
      (ae_of_all _ fun targetCfg => hbound (coord (ctx, targetCfg)))
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean,
    κ, coord] using h

/-- The canonical residual is strongly measurable on the genuine joint
configuration space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual_stronglyMeasurable
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
        H N hN beta hbeta target F) := by
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_stronglyMeasurable
      H N hN beta hbeta target F hF
  have hOuter :=
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
      H N target
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
  exact hF.sub (hMean.comp_measurable hOuter)

/-- For bounded concrete observables the canonical residual belongs to the
genuine ground-state joint L2 space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual_memLp_two
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
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
        H N hN beta hbeta target F)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let residual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
      H N hN beta hbeta target F
  have hResidual :
      StronglyMeasurable residual := by
    simpa [residual] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual_stronglyMeasurable
        H N hN beta hbeta target F hF
  apply MemLp.of_bound hResidual.aestronglyMeasurable (bound + bound)
  exact Filter.Eventually.of_forall fun z => by
    have hMean :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_norm_le_of_bounded
        H N hN beta hbeta target F bound hbound
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
          H N target z)
    calc
      ‖residual z‖ ≤
          ‖F z‖ +
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
              H N hN beta hbeta target F
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                H N target z)‖ := by
        simpa [residual,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual] using
          norm_sub_le (F z)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
              H N hN beta hbeta target F
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                H N target z))
      _ ≤ bound + bound :=
        add_le_add (hbound z) hMean

/-- Canonical genuine-joint L2 localPart vector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
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
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual_memLp_two
    H N hN beta hbeta target F hF bound hbound).toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
        H N hN beta hbeta target F)

/-- The canonical localPart L2 vector has the concrete canonical residual as
its a.e. representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_coeFn
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
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
        H N hN beta hbeta target F hF bound hbound z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
        H N hN beta hbeta target F := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual_memLp_two
      H N hN beta hbeta target F hF bound hbound).coeFn_toLp

/-- The squared norm of the canonical genuine-joint localPart vector is exactly
the canonical genuine target-fiber variance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_norm_sq_ofReal_eq_variance
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
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta target F hF bound hbound‖ ^ 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let residual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual
      H N hN beta hbeta target F
  let r :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
      H N hN beta hbeta target F hF bound hbound
  have hMem :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual_memLp_two
      H N hN beta hbeta target F hF bound hbound
  have hRep :
      (fun z => r z) =ᵐ[μJ] residual := by
    simpa [r, residual, μJ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2] using
      hMem.coeFn_toLp
  have hSq :
      Integrable (fun z => residual z ^ 2) μJ := by
    simpa only [Pi.pow_apply] using hMem.integrable_sq
  have hNorm :
      (∫ z, residual z ^ 2 ∂μJ) = ‖r‖ ^ 2 := by
    calc
      (∫ z, residual z ^ 2 ∂μJ) =
          ∫ z, ‖r z‖ ^ 2 ∂μJ := by
        apply integral_congr_ae
        filter_upwards [hRep] with z hz
        rw [hz]
        simp [Real.norm_eq_abs, sq_abs]
      _ = ‖r‖ ^ 2 :=
        (realL2_norm_sq_eq_integral_norm_sq r).symm
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_eq_joint_canonicalFiberMean_residual_lintegral
      H N hN beta hbeta target F hF
  calc
    ENNReal.ofReal (‖r‖ ^ 2) =
        ENNReal.ofReal (∫ z, residual z ^ 2 ∂μJ) := by
      rw [hNorm]
    _ = ∫⁻ z, ENNReal.ofReal (residual z ^ 2) ∂μJ :=
      ofReal_integral_eq_lintegral_ofReal
        hSq (ae_of_all μJ fun z => sq_nonneg (residual z))
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F := by
      simpa [residual, μJ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidual,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap]
        using hVariance.symm

/-- ENNReal squared-norm form of the coefficient-one localPart estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_norm_sq_ofReal_le_condExpL2_residual_norm_sq_ofReal
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
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta target F hF bound hbound‖ ^ 2) ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  calc
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta target F hF bound hbound‖ ^ 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta target F :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_norm_sq_ofReal_eq_variance
        H N hN beta hbeta target F hF bound hbound
    _ ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
        H N hN beta hbeta target F hF bound hbound

end

end MathlibAnalytic
end MGAP4D
