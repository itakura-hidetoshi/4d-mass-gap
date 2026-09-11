import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathKernel

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A real observable is constant on fibers obtained by forgetting one
physical positive link. -/
def CompactOrientedGaugeWilsonSystem.OffLinkFiberConstant
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (f : L.Configuration → ℝ) : Prop :=
  ∀ A B : L.Configuration,
    L.AgreeOffLink A B target → f A = f B

/-- Exact compact-group one-link conditional expectation viewed as an operator
on real observables. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.base.Configuration → ℝ :=
  fun A => C.singleLinkConditionalExpectation f A target

/-- Exact compact-group heat-bath projection is invariant on every off-link
fiber. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.base.OffLinkFiberConstant target
      (C.singleLinkHeatBathProjection target f) := by
  intro A B hAgree
  exact
    continuous_compact_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
      C f A B target hAgree

end

end MathlibAnalytic
end MGAP4D
