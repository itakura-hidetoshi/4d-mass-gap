import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathJointIntegralSymmetry
namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
noncomputable section

theorem continuous_compact_oriented_singleLinkHeatBathJointMeasure_fst_core
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathJointMeasure target).fst = C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
  exact Measure.fst_compProd C.gibbsMeasure (C.singleLinkHeatBathKernel target)

theorem continuous_compact_oriented_singleLinkHeatBathJointMeasure_snd_core
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (C.singleLinkHeatBathJointMeasure target).snd = C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let J := C.singleLinkHeatBathJointMeasure target
  calc
    J.snd = (Measure.map Prod.swap J).fst := by
      symm
      exact Measure.fst_map_swap
    _ = J.fst := by
      rw [continuous_compact_oriented_map_swap_singleLinkHeatBathJointMeasure C target]
    _ = C.gibbsMeasure :=
      continuous_compact_oriented_singleLinkHeatBathJointMeasure_fst_core C target

theorem continuous_compact_oriented_singleLinkHeatBathKernel_stationary_core
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathKernel target ∘ₘ C.gibbsMeasure = C.gibbsMeasure := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  calc
    C.singleLinkHeatBathKernel target ∘ₘ C.gibbsMeasure =
        (C.singleLinkHeatBathJointMeasure target).snd := by
      symm
      unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathJointMeasure
      exact Measure.snd_compProd C.gibbsMeasure (C.singleLinkHeatBathKernel target)
    _ = C.gibbsMeasure :=
      continuous_compact_oriented_singleLinkHeatBathJointMeasure_snd_core C target

end
end MathlibAnalytic
end MGAP4D
