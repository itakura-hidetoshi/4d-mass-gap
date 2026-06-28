import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Exact one-link conditional expectation of a bounded continuous observable
for a compact oriented Wilson system. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g : C.base.Gauge,
    O (C.base.replaceLink A target g)
      ∂C.singleLinkConditionalMeasure A target

/-- The compact one-link conditional expectation depends only on the
configuration away from the updated physical link. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkConditionalExpectation O A target =
      C.singleLinkConditionalExpectation O B target := by
  have hMeasure :
      C.singleLinkConditionalMeasure A target =
        C.singleLinkConditionalMeasure B target :=
    continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
      C A B target hAgree
  have hReplace :
      (fun g : C.base.Gauge => O (C.base.replaceLink A target g)) =
        fun g : C.base.Gauge => O (C.base.replaceLink B target g) := by
    funext g
    rw [compact_oriented_replaceLink_eq_of_agreeOffLink
      C.base A B target g hAgree]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  rw [hMeasure, hReplace]

/-- Pre-updating the resampled physical link leaves its conditional expectation
unchanged. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalExpectation O
        (C.base.replaceLink A target g) target =
      C.singleLinkConditionalExpectation O A target := by
  apply continuous_compact_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
  intro e he
  exact compact_oriented_replaceLink_of_ne C.base A target e g he

/-- A compact oriented observable is constant on fibers obtained by forgetting
one physical link. -/
def CompactOrientedGaugeWilsonSystem.OffLinkFiberConstant
    (L : CompactOrientedGaugeWilsonSystem)
    (target : L.geometry.Edge)
    (O : L.Configuration → ℝ) : Prop :=
  ∀ A B : L.Configuration,
    L.AgreeOffLink A B target → O A = O B

/-- Exact compact-Haar one-link conditional expectation fixes every observable
already constant on the corresponding off-link fibers. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_fixes
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge)
    (hFiber : C.base.OffLinkFiberConstant target O) :
    ∀ A : C.base.Configuration,
      C.singleLinkConditionalExpectation O A target = O A := by
  intro A
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  have hPoint :
      ∀ g : C.base.Gauge,
        O (C.base.replaceLink A target g) = O A := by
    intro g
    apply hFiber (C.base.replaceLink A target g) A
    intro e he
    exact compact_oriented_replaceLink_of_ne C.base A target e g he
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  simp_rw [hPoint]
  simp

/-- In particular, the compact one-link heat-bath expectation fixes constants. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_const
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalExpectation
        (BoundedContinuousFunction.const _ c) A target = c := by
  apply continuous_compact_oriented_singleLinkConditionalExpectation_fixes
  intro B D hAgree
  rfl

end
end MathlibAnalytic
end MGAP4D
