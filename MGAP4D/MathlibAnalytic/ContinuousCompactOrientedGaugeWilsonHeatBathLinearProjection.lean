import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathContinuity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCF_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O P : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionBCF target (O + P) =
      C.singleLinkHeatBathProjectionBCF target O +
        C.singleLinkHeatBathProjectionBCF target P := by
  ext A
  change C.singleLinkHeatBathProjection target (O + P) A =
    C.singleLinkHeatBathProjection target O A +
      C.singleLinkHeatBathProjection target P A
  exact congrFun
    (continuous_compact_oriented_singleLinkHeatBathProjection_add
      C target O P) A

theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCF_smul
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (c : ℝ)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionBCF target (c • O) =
      c • C.singleLinkHeatBathProjectionBCF target O := by
  ext A
  change C.singleLinkHeatBathProjection target (c • O) A =
    c * C.singleLinkHeatBathProjection target O A
  exact congrFun
    (continuous_compact_oriented_singleLinkHeatBathProjection_smul
      C target c O) A

noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionLinearMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    BoundedContinuousFunction C.base.Configuration ℝ →ₗ[ℝ]
      BoundedContinuousFunction C.base.Configuration ℝ where
  toFun := C.singleLinkHeatBathProjectionBCF target
  map_add' := continuous_compact_oriented_singleLinkHeatBathProjectionBCF_add
    C target
  map_smul' := continuous_compact_oriented_singleLinkHeatBathProjectionBCF_smul
    C target

theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCF_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.base.OffLinkFiberConstant target
      (C.singleLinkHeatBathProjectionBCF target O) := by
  intro A B hAgree
  change C.singleLinkHeatBathProjection target O A =
    C.singleLinkHeatBathProjection target O B
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_of_agreeOffLink
      C O A B target hAgree

theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCF_fixes
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hFiber : C.base.OffLinkFiberConstant target O) :
    C.singleLinkHeatBathProjectionBCF target O = O := by
  ext A
  change C.singleLinkHeatBathProjection target O A = O A
  exact continuous_compact_oriented_singleLinkConditionalExpectation_fixes
    C O target hFiber A

theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCF_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionBCF target
        (C.singleLinkHeatBathProjectionBCF target O) =
      C.singleLinkHeatBathProjectionBCF target O := by
  exact continuous_compact_oriented_singleLinkHeatBathProjectionBCF_fixes
    C target (C.singleLinkHeatBathProjectionBCF target O)
    (continuous_compact_oriented_singleLinkHeatBathProjectionBCF_offLinkFiberConstant
      C target O)

end
end MathlibAnalytic
end MGAP4D
