import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberPosteriorJointAEBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalMeanCondExpIdentification
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Explicit posterior action on the genuine ground-state joint L2 carrier

PR #5209 identifies historical normalized one-link fiber laws with the
continuous posterior conditional laws under the actual joint measure.
PR #4931 identifies the canonical fiber mean with genuine joint CondExpL2.

We connect these two results without replacing the law or the Hilbert space.
The integrand-independent canonical kernel identity is pulled back along the
retained-context map.  Singleton target evaluation then pushes that kernel to
the posterior conditional measure.  The measurable-equivalence integral
formula identifies the canonical mean with the explicit posterior integral.

Consequently the literal posterior integral is an a.e. representative of the
EXISTING joint CondExpL2 on the bounded strongly measurable core.  The resulting
MemLp class is constructed from the formula and proved equal to that projection.
The observable may depend on both boundaries, not only on the right one.
A final corollary specializes to the existing right-boundary posterior BCF API.

All model statements hold for N > 0 and beta >= 0.  No extra cutoff,
comparison constant, fiber-independence premise or representative choice is
introduced.  The common kernel/mean event is independent of the integrand.
The arbitrary-test mean equality uses mathlib's totalized Bochner integral;
the L2/projection assertions are restricted to bounded strongly measurable F.

This does not assert a stagewise oscillation tail, cross-scale physicality,
physical-transfer/reconstruction commutation, or posterior-sweep/Euclidean-time
identification.  The strict-interval scaling no-go remains unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
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

namespace GroundStatePosteriorJoint

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Joint" => Cfg × Cfg
local notation "μH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta

/-- The literal posterior target-link integral of a joint observable. -/
def posteriorMean (target : Link) (F : Joint → ℝ) (z : Joint) : ℝ :=
  ∫ g, F (z.1, Function.update z.2 target g)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      H N hN beta hbeta z.1 z.2 target

private theorem outerContext_pairHaar_quasiMeasurePreserving (target : Link) :
    Measure.QuasiMeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target)
      (μH.prod μH)
      (μH.prod (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar Gauge))) := by
  classical
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar Gauge)
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar Gauge)
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  have hcoord :
      MeasurePreserving coord ((μH.prod μOff).prod μTarget) (μH.prod μH) := by
    simpa [coord, μOff, μTarget] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
        H N target)
  change Measure.QuasiMeasurePreserving (Prod.fst ∘ coord.symm)
    (μH.prod μH) (μH.prod μOff)
  exact (Measure.quasiMeasurePreserving_fst (μ := μH.prod μOff) (ν := μTarget)).comp
    hcoord.symm.quasiMeasurePreserving

/-- Evaluation pushes the actual canonical split kernel to the posterior law
joint-almost everywhere.  The event does not depend on an observable. -/
theorem canonicalKernel_map_joint_ae_eq_posterior (target : Link) :
    ∀ᵐ z ∂μJ,
      Measure.map
          (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
            (Gauge := Gauge) target)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target z)) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta z.1 z.2 target := by
  have hContext :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel_ae_eq_normalizedFiber
      H N hN beta hbeta target
  have hHaar := (outerContext_pairHaar_quasiMeasurePreserving H N target).ae hContext
  have hAC : μJ ≪ μH.prod μH := withDensity_absolutelyContinuous _ _
  have hJoint := hHaar.filter_mono hAC.ae_le
  filter_upwards [hJoint,
    GroundStatePosteriorFiberBridge.normalizedFiberMeasure_joint_ae_eq_posterior
      H N hN beta hbeta target] with z hk hp
  rw [hk]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_map_targetEvaluation_eq_directNormalizedFiberMeasure
      H N hN beta hbeta z.1 z.2 target).trans hp

/-- A single full-measure joint event identifies all canonical means with the
literal posterior integrals.  No measurability premise is needed for this
change of variables between totalized Bochner integrals. -/
theorem canonicalMean_joint_ae_eq_posteriorMean (target : Link) :
    ∀ᵐ z ∂μJ, ∀ F : Joint → ℝ,
      GroundStateCanonicalMean.canonicalMean H N hN beta hbeta target F z =
        posteriorMean H N hN beta hbeta target F z := by
  filter_upwards [canonicalKernel_map_joint_ae_eq_posterior
    H N hN beta hbeta target] with z hz
  intro F
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Gauge) target
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetCanonicalMarkovKernel
      H N hN beta hbeta target
  let outer := periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target
  let coord :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
      H N target
  let f : Gauge → ℝ := fun g => F (z.1, Function.update z.2 target g)
  change (∫ targetCfg, F (coord (outer z, targetCfg)) ∂κ (outer z)) =
    ∫ g, f g
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta z.1 z.2 target
  calc
    (∫ targetCfg, F (coord (outer z, targetCfg)) ∂κ (outer z)) =
        ∫ targetCfg, f (eval targetCfg) ∂κ (outer z) := by
      apply integral_congr_ae
      filter_upwards with targetCfg
      change F (z.1,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Gauge) target).symm
            (targetCfg, periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.2)) =
        F (z.1, Function.update z.2 target (eval targetCfg))
      exact congrArg (fun right : Cfg => F (z.1, right))
        (periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update
          target z.2 targetCfg)
    _ = ∫ g, f g ∂Measure.map eval (κ (outer z)) :=
      (integral_map_equiv eval f).symm
    _ = ∫ g, f g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
          H N hN beta hbeta z.1 z.2 target := by
      rw [hz]

/-- On the bounded strongly measurable joint core, the explicit posterior
integral represents the existing genuine joint CondExpL2. -/
theorem condExpL2_coeFn_eq_posteriorMean (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound) z) =ᵐ[μJ]
      posteriorMean H N hN beta hbeta target F := by
  exact (GroundStateCanonicalMean.condExpL2_coeFn_eq_canonicalMean
    H N hN beta hbeta target F hF bound hbound).trans
    ((canonicalMean_joint_ae_eq_posteriorMean H N hN beta hbeta target).mono
      fun z hz => hz F)

/-- The explicit formula, not a chosen projection representative, belongs to
the actual joint L2 space on the bounded strongly measurable core. -/
theorem posteriorMean_memLp_two (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    MemLp (posteriorMean H N hN beta hbeta target F) 2 μJ := by
  exact (Lp.memLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound))).congr
    (condExpL2_coeFn_eq_posteriorMean H N hN beta hbeta target F hF bound hbound)

/-- The existing joint L2 class of the literal posterior formula. -/
def posteriorMeanL2 (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) : JL2 :=
  (posteriorMean_memLp_two H N hN beta hbeta target F hF bound hbound).toLp
    (posteriorMean H N hN beta hbeta target F)

/-- Exact identification in the existing Hilbert carrier, without comparison
loss or an additional posterior/physical operator compatibility assumption. -/
theorem posteriorMeanL2_eq_condExpL2 (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    posteriorMeanL2 H N hN beta hbeta target F hF bound hbound =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound) := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp
    (posteriorMean_memLp_two H N hN beta hbeta target F hF bound hbound)).trans
    (condExpL2_coeFn_eq_posteriorMean H N hN beta hbeta target F hF bound hbound).symm

/-- The pre-existing posterior BCF action is the genuine joint projection of
the right-boundary lift.  Its measurability and bound come from the BCF itself. -/
theorem condExpL2_coeFn_eq_posteriorBCF (target : Link)
    (O : BoundedContinuousFunction Cfg ℝ) :
    (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta (fun w : Joint => O w.2)
        (O.continuous.stronglyMeasurable.comp_measurable measurable_snd)
        ‖O‖ (fun w => O.norm_coe_le_norm w.2)) z) =ᵐ[μJ]
      fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta z.1 O z.2 target := by
  refine (condExpL2_coeFn_eq_posteriorMean H N hN beta hbeta target
    (fun w : Joint => O w.2)
    (O.continuous.stronglyMeasurable.comp_measurable measurable_snd)
    ‖O‖ (fun w => O.norm_coe_le_norm w.2)).trans ?_
  filter_upwards with z
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral
      H N hN beta hbeta z.1 O z.2 target).symm

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
