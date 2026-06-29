import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathContinuousLinearLaws

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweepBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ •
    ∑ target : C.base.geometry.Edge,
      C.singleLinkHeatBathProjectionBCF target O

@[simp] theorem continuous_compact_oriented_randomScanHeatBathSweepBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.randomScanHeatBathSweepBCF O A =
      C.randomScanHeatBathSweep O A := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweepBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweep]

noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathContinuousLinearMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    BoundedContinuousFunction C.base.Configuration ℝ →L[ℝ]
      BoundedContinuousFunction C.base.Configuration ℝ :=
  (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ •
    ∑ target : C.base.geometry.Edge,
      C.singleLinkHeatBathProjectionContinuousLinearMap target

@[simp] theorem continuous_compact_oriented_randomScanHeatBathContinuousLinearMap_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.randomScanHeatBathContinuousLinearMap O =
      C.randomScanHeatBathSweepBCF O := by
  ext A
  simp [ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathContinuousLinearMap,
    ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweepBCF]

theorem continuous_compact_oriented_randomScanHeatBathSweepBCF_const
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (c : ℝ) :
    C.randomScanHeatBathSweepBCF
        (BoundedContinuousFunction.const C.base.Configuration c) =
      BoundedContinuousFunction.const C.base.Configuration c := by
  ext A
  rw [continuous_compact_oriented_randomScanHeatBathSweepBCF_apply]
  change C.randomScanHeatBathSweep
      (BoundedContinuousFunction.const C.base.Configuration c) A = c
  exact congrFun
    (continuous_compact_oriented_randomScanHeatBathSweep_const C hEdge c) A

end
end MathlibAnalytic
end MGAP4D
