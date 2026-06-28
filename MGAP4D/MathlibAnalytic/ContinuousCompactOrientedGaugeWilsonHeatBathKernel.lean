import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkKernel
import Mathlib.Probability.Kernel.Composition.Prod

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Configuration-to-configuration Markov kernel obtained by exact Haar
resampling of one physical positive link. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel C.base.Configuration C.base.Configuration :=
  (Kernel.id ×ₖ C.singleLinkConditionalKernel target).map
    (fun z : C.base.Configuration × C.base.Gauge =>
      C.base.replaceLink z.1 target z.2)

/-- Exact one-link Haar resampling is a Markov kernel on the full physical-link
configuration space. -/
instance continuousCompactOriented_singleLinkHeatBathKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.singleLinkHeatBathKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathKernel
  exact IsMarkovKernel.map
    (Kernel.id ×ₖ C.singleLinkConditionalKernel target)
    (continuous_compact_oriented_replaceLink_uncurry C target).measurable

/-- Lebesgue-integral formula for one exact compact-group heat-bath update. -/
theorem continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (f : C.base.Configuration → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ B, f B ∂C.singleLinkHeatBathKernel target A =
      ∫⁻ g, f (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathKernel,
    Kernel.lintegral_map _
      (continuous_compact_oriented_replaceLink_uncurry C target).measurable
      A hf,
    Kernel.lintegral_id_prod]
  · rw [continuous_compact_oriented_singleLinkConditionalKernel_apply]
  · exact hf.comp
      (continuous_compact_oriented_replaceLink_uncurry C target).measurable

/-- Pointwise pushforward description of the exact compact heat-bath update
measure. -/
theorem continuous_compact_oriented_singleLinkHeatBathKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathKernel target A =
      (C.singleLinkConditionalMeasure A target).map
        (fun g : C.base.Gauge =>
          C.base.replaceLink A target g) := by
  ext s hs
  rw [← MeasureTheory.lintegral_indicator hs,
    continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
      C target A (s.indicator 1)
      (measurable_const.indicator hs),
    MeasureTheory.lintegral_map]
  · rfl
  · exact (continuous_compact_oriented_replaceLink C A target).measurable
  · exact measurable_const.indicator hs

end

end MathlibAnalytic
end MGAP4D
