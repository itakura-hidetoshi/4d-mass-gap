import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionIdempotent
import Mathlib.Probability.Kernel.Composition.Comp

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The expectation produced by one exact compact heat-bath update is
unchanged if the input configuration is first modified at the same link. -/
theorem continuous_compact_oriented_lintegral_singleLinkHeatBathKernel_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (A : C.base.Configuration)
    (g : C.base.Gauge)
    (f : C.base.Configuration → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ B, f B
        ∂C.singleLinkHeatBathKernel target
          (C.base.replaceLink A target g) =
      ∫⁻ B, f B ∂C.singleLinkHeatBathKernel target A := by
  rw [continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
      C target (C.base.replaceLink A target g) f hf,
    continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
      C target A f hf,
    continuous_compact_oriented_singleLinkConditionalMeasure_replaceLink]
  apply lintegral_congr
  intro h
  rw [compact_oriented_replaceLink_replaceLink]

/-- The exact compact-group one-link heat-bath Markov kernel is idempotent. -/
theorem continuous_compact_oriented_singleLinkHeatBathKernel_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathKernel target ∘ₖ
        C.singleLinkHeatBathKernel target =
      C.singleLinkHeatBathKernel target := by
  apply Kernel.ext_fun
  intro A f hf
  rw [Kernel.lintegral_comp _ _ A hf,
    continuous_compact_oriented_lintegral_singleLinkHeatBathKernel
      C target A
      (fun B => ∫⁻ D, f D ∂C.singleLinkHeatBathKernel target B)
      hf.lintegral_kernel]
  letI : IsProbabilityMeasure
      (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  calc
    ∫⁻ g,
        (∫⁻ D, f D
          ∂C.singleLinkHeatBathKernel target
            (C.base.replaceLink A target g))
        ∂C.singleLinkConditionalMeasure A target =
      ∫⁻ _g,
        (∫⁻ D, f D ∂C.singleLinkHeatBathKernel target A)
        ∂C.singleLinkConditionalMeasure A target := by
          apply lintegral_congr
          intro g
          exact
            continuous_compact_oriented_lintegral_singleLinkHeatBathKernel_replaceLink
              C target A g f hf
    _ = ∫⁻ D, f D ∂C.singleLinkHeatBathKernel target A := by
      simp

end

end MathlibAnalytic
end MGAP4D
