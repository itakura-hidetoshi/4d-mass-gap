import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathContinuousLinearLaws

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact finite-link random-scan heat-bath sweep as a bounded continuous
observable. -/
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

/-- Exact compact random-scan heat-bath sweep as a continuous real-linear
operator on bounded continuous observables. -/
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

/-- A nonempty physical-link set makes the bounded-continuous compact
random-scan heat-bath operator fix constants exactly. -/
theorem continuous_compact_oriented_randomScanHeatBathSweepBCF_const
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (c : ℝ) :
    C.randomScanHeatBathSweepBCF
        (BoundedContinuousFunction.const C.base.Configuration c) =
      BoundedContinuousFunction.const C.base.Configuration c := by
  ext A
  change C.randomScanHeatBathSweep
      (BoundedContinuousFunction.const C.base.Configuration c) A = c
  exact congrFun
    (continuous_compact_oriented_randomScanHeatBathSweep_const C hEdge c) A

end
end MathlibAnalytic
end MGAP4D
