import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathProjectionCore

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Exact compact one-link conditional expectation fixes every observable
already constant on the corresponding off-link fibers. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_fixes
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ)
    (hFiber : C.base.OffLinkFiberConstant target f) :
    C.singleLinkHeatBathProjection target f = f := by
  funext A
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  letI : IsProbabilityMeasure
      (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  calc
    ∫ g, f (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target =
      ∫ _g, f A ∂C.singleLinkConditionalMeasure A target := by
        apply integral_congr_ae
        filter_upwards [] with g
        apply hFiber (C.base.replaceLink A target g) A
        intro e he
        simp [CompactOrientedGaugeWilsonSystem.replaceLink, he]
    _ = f A := by simp

/-- The compact-group one-link heat-bath projection is idempotent. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.singleLinkHeatBathProjection target
        (C.singleLinkHeatBathProjection target f) =
      C.singleLinkHeatBathProjection target f :=
  continuous_compact_oriented_singleLinkHeatBathProjection_fixes
    C target (C.singleLinkHeatBathProjection target f)
    (continuous_compact_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
      C target f)

/-- Fixed points of compact one-link heat-bath resampling are exactly the
off-link-fiber-constant observables. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_fixed_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : C.base.Configuration → ℝ) :
    C.singleLinkHeatBathProjection target f = f ↔
      C.base.OffLinkFiberConstant target f := by
  constructor
  · intro hFix
    rw [← hFix]
    exact
      continuous_compact_oriented_singleLinkHeatBathProjection_offLinkFiberConstant
        C target f
  · exact
      continuous_compact_oriented_singleLinkHeatBathProjection_fixes
        C target f

end

end MathlibAnalytic
end MGAP4D
