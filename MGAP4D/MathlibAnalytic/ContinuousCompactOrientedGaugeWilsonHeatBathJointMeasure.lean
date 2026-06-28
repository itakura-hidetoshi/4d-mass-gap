import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathReversibility
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Joint law of the old and newly sampled physical-link configurations for
one exact compact-group heat-bath update. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure (C.base.Configuration × C.base.Configuration) :=
  C.gibbsMeasure ⊗ₘ C.singleLinkHeatBathKernel target

/-- The one-link heat-bath joint law is a probability measure. -/
instance continuousCompactOriented_singleLinkHeatBathJointMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure (C.singleLinkHeatBathJointMeasure target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
  infer_instance

/-- Integration against the joint transition law is the Gibbs-weighted
transition integral. -/
theorem continuous_compact_oriented_lintegral_singleLinkHeatBathJointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (Phi : C.base.Configuration × C.base.Configuration → ℝ≥0∞)
    (hPhi : Measurable Phi) :
    ∫⁻ z, Phi z ∂C.singleLinkHeatBathJointMeasure target =
      C.singleLinkHeatBathTransitionLIntegral target Phi := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransitionLIntegral
  exact Measure.lintegral_compProd hPhi

/-- The exact compact-group heat-bath joint law is invariant under exchanging
old and newly sampled configurations. -/
theorem continuous_compact_oriented_map_swap_singleLinkHeatBathJointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.swap (C.singleLinkHeatBathJointMeasure target) =
      C.singleLinkHeatBathJointMeasure target := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_swap hs]
  have hPre : MeasurableSet (Prod.swap ⁻¹' s) := measurable_swap hs
  have hIndicator : Measurable (s.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hs
  have hSymm :=
    continuous_compact_oriented_singleLinkHeatBathTransitionLIntegral_symm
      C target (s.indicator (fun _ => (1 : ℝ≥0∞))) hIndicator
  calc
    C.singleLinkHeatBathJointMeasure target (Prod.swap ⁻¹' s) =
        ∫⁻ z,
          (Prod.swap ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) z
          ∂C.singleLinkHeatBathJointMeasure target := by
      rw [lintegral_indicator_one hPre]
    _ = ∫⁻ z,
        s.indicator (fun _ => (1 : ℝ≥0∞)) z.swap
        ∂C.singleLinkHeatBathJointMeasure target := by
      apply lintegral_congr
      intro z
      by_cases hz : z.swap ∈ s
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_not_mem hz]
    _ = C.singleLinkHeatBathTransitionLIntegral target
        (fun z => s.indicator (fun _ => (1 : ℝ≥0∞)) z.swap) :=
      continuous_compact_oriented_lintegral_singleLinkHeatBathJointMeasure
        C target _ (hIndicator.comp measurable_swap)
    _ = C.singleLinkHeatBathTransitionLIntegral target
        (s.indicator (fun _ => (1 : ℝ≥0∞))) := hSymm.symm
    _ = ∫⁻ z,
        s.indicator (fun _ => (1 : ℝ≥0∞)) z
        ∂C.singleLinkHeatBathJointMeasure target :=
      (continuous_compact_oriented_lintegral_singleLinkHeatBathJointMeasure
        C target _ hIndicator).symm
    _ = C.singleLinkHeatBathJointMeasure target s :=
      lintegral_indicator_one hs

end

end MathlibAnalytic
end MGAP4D
