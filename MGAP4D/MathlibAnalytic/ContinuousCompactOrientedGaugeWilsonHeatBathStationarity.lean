import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointIntegralSymmetry

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- The first marginal of the exact one-link heat-bath joint law is the Wilson
Gibbs measure. -/
theorem continuous_compact_oriented_singleLinkHeatBathJointMeasure_fst
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathJointMeasure target).fst = C.gibbsMeasure := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
  exact Measure.fst_compProd C.gibbsMeasure
    (C.singleLinkHeatBathKernel target)

/-- Reversibility identifies the second marginal of the one-link heat-bath
joint law with the Wilson Gibbs measure. -/
theorem continuous_compact_oriented_singleLinkHeatBathJointMeasure_snd
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathJointMeasure target).snd = C.gibbsMeasure := by
  let J := C.singleLinkHeatBathJointMeasure target
  calc
    J.snd = (Measure.map Prod.swap J).fst := by
      symm
      exact Measure.fst_map_swap
    _ = J.fst := by
      rw [continuous_compact_oriented_map_swap_singleLinkHeatBathJointMeasure
        C target]
    _ = C.gibbsMeasure :=
      continuous_compact_oriented_singleLinkHeatBathJointMeasure_fst
        C target

/-- The orientation-correct Wilson Gibbs law is stationary for every exact
compact-group one-link heat-bath kernel. -/
theorem continuous_compact_oriented_singleLinkHeatBathKernel_stationary
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathKernel target ∘ₘ C.gibbsMeasure =
      C.gibbsMeasure := by
  calc
    C.singleLinkHeatBathKernel target ∘ₘ C.gibbsMeasure =
        (C.singleLinkHeatBathJointMeasure target).snd := by
      symm
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
      exact Measure.snd_compProd C.gibbsMeasure
        (C.singleLinkHeatBathKernel target)
    _ = C.gibbsMeasure :=
      continuous_compact_oriented_singleLinkHeatBathJointMeasure_snd
        C target

end

end MathlibAnalytic
end MGAP4D
