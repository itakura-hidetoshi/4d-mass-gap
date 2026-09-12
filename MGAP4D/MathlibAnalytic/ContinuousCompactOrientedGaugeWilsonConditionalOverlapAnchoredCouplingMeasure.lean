import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapAnchoredTransitionKernel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The left-anchored overlap transition specialized to one fixed pair of
background configurations. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredOverlapTransitionKernelAt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    Kernel C.base.Gauge C.base.Gauge :=
  (C.configurationPairConditionalAnchoredOverlapTransitionKernel target).comap
    (fun g : C.base.Gauge => (z, g))
    (measurable_const.prodMk measurable_id)

/-- The fixed-background transition fiber is the original anchored transition
at the corresponding background/anchor input. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernelAt_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge) :
    C.configurationPairConditionalAnchoredOverlapTransitionKernelAt target z g =
      C.configurationPairConditionalAnchoredOverlapTransitionKernel target (z, g) := by
  rfl

/-- Exact diagonal/residual fiber formula after specializing the background
pair. -/
theorem continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernelAt_apply_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge) :
    C.configurationPairConditionalAnchoredOverlapTransitionKernelAt target z g =
      C.configurationPairConditionalAnchoredDiagonalWeight target (z, g) •
          Measure.dirac g +
        C.configurationPairConditionalAnchoredResidualWeight target (z, g) •
          C.configurationPairConditionalAnchoredNormalizedRightResidualMeasure
            target (z, g) := by
  rw [continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernelAt_apply,
    continuous_compact_oriented_configurationPairConditionalAnchoredOverlapTransitionKernel_apply]

/-- Every fixed-background anchored transition remains Markov. -/
instance continuousCompactOriented_configurationPairConditionalAnchoredOverlapTransitionKernelAt_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    IsMarkovKernel
      (C.configurationPairConditionalAnchoredOverlapTransitionKernelAt target z) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredOverlapTransitionKernelAt
  infer_instance

/-- Joint law obtained by starting from the exact left conditional target-link
law and applying the explicit left-anchored overlap transition. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredOverlapCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure (C.base.Gauge × C.base.Gauge) :=
  C.singleLinkConditionalMeasure A target ⊗ₘ
    C.configurationPairConditionalAnchoredOverlapTransitionKernelAt target (A, B)

/-- The anchored joint law is a probability measure. -/
instance continuousCompactOriented_singleLinkConditionalAnchoredOverlapCouplingMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.singleLinkConditionalAnchoredOverlapCouplingMeasure A B target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredOverlapCouplingMeasure
  infer_instance

/-- The anchored joint law has total mass one. -/
theorem continuous_compact_oriented_singleLinkConditionalAnchoredOverlapCouplingMeasure_univ
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalAnchoredOverlapCouplingMeasure A B target univ = 1 := by
  exact measure_univ

/-- The first marginal of the anchored joint law is exactly the left
conditional target-link law. -/
theorem continuous_compact_oriented_fst_singleLinkConditionalAnchoredOverlapCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    (C.singleLinkConditionalAnchoredOverlapCouplingMeasure A B target).fst =
      C.singleLinkConditionalMeasure A target := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalAnchoredOverlapCouplingMeasure
  exact Measure.fst_compProd _ _

end

end MathlibAnalytic
end MGAP4D
