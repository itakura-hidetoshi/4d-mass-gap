import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMeanCondExpIdentification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectFiberBridge
import Mathlib.Tactic

/-!
# One-link oscillation bounds the genuine ground-state joint CondExpL2 residual

The current Dobrushin/locality lane produces linkwise oscillation bounds for
concrete observables.  The adjacent reconstruction lane, however, uses the
genuine ground-state joint one-link conditional-expectation residual in L2.

This file closes that direction on the bounded-concrete core.

First, if a bounded concrete observable F stays within radius delta of any
retained-outer-context center C, then the canonical one-link fiber variance is
at most delta^2.  The already-proved exact canonical-mean identification turns
that variance into the genuine CondExpL2 residual norm.

Second, a canonical center is obtained by setting the selected target-link
coordinate to the group identity while keeping the complete left boundary and
all off-target right coordinates fixed.  Therefore any ordinary target-link
oscillation bound immediately implies the required centered-radius bound.

The result is the continuous compact ground-state-joint analogue of the finite
heat-bath fact that a one-link projection residual is bounded by the declared
link variation.  No regular-conditional-distribution identification, transfer
identification, Euclidean-time interpretation, or H1-D5 exact descent is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
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

/-- A concrete target-link oscillation bound: replacing only the selected
right-boundary link changes the observable by at most delta. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteOscillationBoundedBy
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (delta : ℝ) : Prop :=
  ∀
    (left right :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ),
    |F (left, right) -
      F (left, Function.update right target g)| ≤ delta

/-- Canonical retained-context center obtained by setting the target link to
the identity while preserving the complete left boundary and all off-target
right coordinates. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target → ℝ :=
  fun ctx =>
    F
      (ctx.1,
        (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
          ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm 1,
            ctx.2))

/-- The canonical unit center is strongly measurable whenever F is. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter_stronglyMeasurable
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter
        H N target F) := by
  let split :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let eval :=
    periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  have hTarget :
      Measurable
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
            H N target =>
          eval.symm (1 : Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    measurable_const
  have hTargetRetained :
      Measurable
        (fun ctx :
          PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
            H N target =>
          (eval.symm (1 : Matrix.specialUnitaryGroup (Fin N) ℂ), ctx.2)) :=
    hTarget.prodMk measurable_snd
  have hRight :
      Measurable
        (fun ctx :
          PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
            H N target =>
          split.symm
            (eval.symm (1 : Matrix.specialUnitaryGroup (Fin N) ℂ), ctx.2)) :=
    split.symm.measurable.comp hTargetRetained
  have hJoint :
      Measurable
        (fun ctx :
          PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
            H N target =>
          (ctx.1,
            split.symm
              (eval.symm (1 : Matrix.specialUnitaryGroup (Fin N) ℂ), ctx.2))) :=
    measurable_fst.prodMk hRight
  simpa [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter,
    split, eval
  ] using hF.comp_measurable hJoint

/-- Evaluating the canonical unit center on the retained context of a complete
joint configuration is exactly evaluation of F after replacing the target
right-boundary link by the group identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter_outerContextMap_eq_update_one
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter
        H N target F
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
          H N target z) =
      F (z.1, Function.update z.2 target 1) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
  rw [
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update]
  simp

/-- A target-link oscillation bound gives the required joint pointwise radius
around the canonical retained-context unit center. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteOscillationBoundedBy.centered_unitCenter
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (delta : ℝ)
    (hOsc :
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteOscillationBoundedBy
        H N target F delta) :
    ∀ z,
      |F z -
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter
          H N target F
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
            H N target z)| ≤ delta := by
  intro z
  rw [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter_outerContextMap_eq_update_one]
  exact hOsc z.1 z.2 1

/-- A bounded concrete observable lying pointwise within radius delta of a
strongly measurable retained-context center has genuine one-link CondExpL2
residual squared at most delta squared. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_condExpL2_residual_sq_le_of_outerCenteredRadius
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
    (C :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target → ℝ)
    (hC : StronglyMeasurable C)
    (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hRadius :
      ∀ z,
        |F z -
          C
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
              H N target z)| ≤ delta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound)‖ ^ 2 ≤
      delta ^ 2 := by
  let μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let f :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound
  let residual :=
    f -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target f
  let variance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
      H N hN beta hbeta target F
  let centered :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
      H N hN beta hbeta target F C
  letI : IsProbabilityMeasure μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  have hVarEq :
      variance = ENNReal.ofReal (‖residual‖ ^ 2) := by
    simpa [variance, residual, f] using
      (GroundStateCanonicalMean.canonicalVariance_eq_condExpResidualNormSq
        H N hN beta hbeta target F hF bound hbound)
  have hVarLe : variance ≤ centered := by
    simpa [variance, centered] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_centeredResidual
        H N hN beta hbeta target F hF bound hbound C)
  have hCenteredEq :
      centered =
        ∫⁻ z,
          ENNReal.ofReal
            ((F z -
              C
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target z)) ^ 2)
          ∂μJ := by
    simpa [centered, μJ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional_eq_joint_lintegral
        H N hN beta hbeta target F hF C hC)
  have hPointSq :
      ∀ z,
        (F z -
          C
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
              H N target z)) ^ 2 ≤
          delta ^ 2 := by
    intro z
    have hAbs := hRadius z
    have hSqAbs :
        |F z -
          C
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
              H N target z)| ^ 2 ≤
          delta ^ 2 := by
      nlinarith [
        abs_nonneg
          (F z -
            C
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                H N target z))]
    simpa [sq_abs] using hSqAbs
  have hLin :
      (∫⁻ z,
        ENNReal.ofReal
          ((F z -
            C
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                H N target z)) ^ 2)
        ∂μJ) ≤
      ENNReal.ofReal (delta ^ 2) := by
    calc
      (∫⁻ z,
          ENNReal.ofReal
            ((F z -
              C
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
                  H N target z)) ^ 2)
          ∂μJ) ≤
        ∫⁻ _z, ENNReal.ofReal (delta ^ 2) ∂μJ := by
          apply lintegral_mono
          intro z
          exact ENNReal.ofReal_le_ofReal (hPointSq z)
      _ = ENNReal.ofReal (delta ^ 2) := by
        simp [μJ]
  have hENN :
      ENNReal.ofReal (‖residual‖ ^ 2) ≤
        ENNReal.ofReal (delta ^ 2) := by
    rw [← hVarEq]
    exact hVarLe.trans (hCenteredEq.trans_le hLin)
  have hReal :
      ‖residual‖ ^ 2 ≤ delta ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg delta)).mp hENN
  simpa [residual, f] using hReal

/-- Direct continuous-ground-state analogue of the finite heat-bath residual
variation bound: a target-link oscillation bound by delta implies that the
squared genuine one-link CondExpL2 residual is at most delta squared. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_condExpL2_residual_sq_le_of_oscillation
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
    (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hOsc :
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteOscillationBoundedBy
        H N target F delta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound)‖ ^ 2 ≤
      delta ^ 2 := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter
      H N target F
  have hC : StronglyMeasurable C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkCanonicalUnitCenter_stronglyMeasurable
        H N target F hF
  have hRadius :
      ∀ z,
        |F z -
          C
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
              H N target z)| ≤ delta := by
    intro z
    simpa [C] using
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteOscillationBoundedBy.centered_unitCenter
        H N target F delta hOsc z)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_condExpL2_residual_sq_le_of_outerCenteredRadius
      H N hN beta hbeta target F hF bound hbound
      C hC delta hdelta hRadius

end

end MathlibAnalytic
end MGAP4D
