import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem continuous_compact_oriented_singleLinkHeatBathProjectionContinuousLinearMap_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionContinuousLinearMap target
        (C.singleLinkHeatBathProjectionContinuousLinearMap target O) =
      C.singleLinkHeatBathProjectionContinuousLinearMap target O := by
  simpa using
    continuous_compact_oriented_singleLinkHeatBathProjectionBCF_idempotent
      C target O

theorem continuous_compact_oriented_singleLinkHeatBathProjectionContinuousLinearMap_norm_le_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    ‖C.singleLinkHeatBathProjectionContinuousLinearMap target‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (by norm_num)
  intro O
  simpa using
    continuous_compact_oriented_singleLinkHeatBathProjectionBCF_norm_le
      C target O

end
end MathlibAnalytic
end MGAP4D
