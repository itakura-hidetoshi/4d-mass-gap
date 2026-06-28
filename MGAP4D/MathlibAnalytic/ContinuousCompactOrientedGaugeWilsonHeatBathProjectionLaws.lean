import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathOperator

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- The exact compact one-link heat-bath projection depends only on the
configuration outside the updated physical link. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkHeatBathProjection target O A =
      C.singleLinkHeatBathProjection target O B := by
  exact
    continuous_compact_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
      C O A B target hAgree

/-- The exact compact one-link heat-bath projection is constant on every
configuration fiber obtained by forgetting the updated link. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    C.base.OffLinkFiberConstant target
      (C.singleLinkHeatBathProjection target O) := by
  intro A B hAgree
  exact
    continuous_compact_oriented_singleLinkHeatBathProjection_eq_of_agreeOffLink
      C O A B target hAgree

/-- The compact one-link heat-bath projection fixes every bounded continuous
observable already constant on the corresponding off-link fibers. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_fixes
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge)
    (hFiber : C.base.OffLinkFiberConstant target O) :
    C.singleLinkHeatBathProjection target O = O := by
  funext A
  exact continuous_compact_oriented_singleLinkConditionalExpectation_fixes
    C O target hFiber A

/-- Applying the same exact compact conditional expectation after a target-link
replacement gives the same projected value. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkHeatBathProjection target O
        (C.base.replaceLink A target g) =
      C.singleLinkHeatBathProjection target O A := by
  exact continuous_compact_oriented_singleLinkConditionalExpectation_replaceLink
    C O A target g

/-- Kernel-level idempotence: averaging a projected observable once more over
the same exact compact conditional law leaves its value unchanged. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_integral_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    (∫ g : C.base.Gauge,
      C.singleLinkHeatBathProjection target O
        (C.base.replaceLink A target g)
      ∂C.singleLinkConditionalMeasure A target) =
      C.singleLinkHeatBathProjection target O A := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  simp_rw [continuous_compact_oriented_singleLinkHeatBathProjection_replaceLink]
  simp

end
end MathlibAnalytic
end MGAP4D
