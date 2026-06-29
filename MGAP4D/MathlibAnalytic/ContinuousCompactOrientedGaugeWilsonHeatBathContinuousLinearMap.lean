import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathNormContraction
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private theorem compact_heatBath_linear_bound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    ‖C.singleLinkHeatBathProjectionLinearMap target O‖ ≤
      (1 : ℝ) * ‖O‖ := by
  simpa using
    continuous_compact_oriented_singleLinkHeatBathProjectionBCF_norm_le
      C target O

noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionContinuousLinearMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    BoundedContinuousFunction C.base.Configuration ℝ →L[ℝ]
      BoundedContinuousFunction C.base.Configuration ℝ :=
  LinearMap.mkContinuous
    (𝕜 := ℝ)
    (𝕜₂ := ℝ)
    (E := BoundedContinuousFunction C.base.Configuration ℝ)
    (F := BoundedContinuousFunction C.base.Configuration ℝ)
    (σ := RingHom.id ℝ)
    (C.singleLinkHeatBathProjectionLinearMap target)
    1
    (compact_heatBath_linear_bound C target)

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathProjectionContinuousLinearMap_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionContinuousLinearMap target O =
      C.singleLinkHeatBathProjectionBCF target O := by
  rfl

end
end MathlibAnalytic
end MGAP4D
