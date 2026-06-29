import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkDensity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Density-based total variation between two exact compact-Haar one-link
conditional Gibbs laws. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  (2 : ℝ)⁻¹ *
    ∫ g : C.base.Gauge,
      |C.singleLinkConditionalDensity A target g -
        C.singleLinkConditionalDensity B target g|
      ∂normalizedCompactHaar C.base.Gauge

/-- Compact-Haar one-link conditional total variation is nonnegative. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    0 ≤ C.singleLinkConditionalTotalVariation A B target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
  exact mul_nonneg (by positivity)
    (integral_nonneg fun g => abs_nonneg _)

/-- Exact zero total variation on a common off-target configuration fiber. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkConditionalTotalVariation A B target = 0 := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
  rw [continuous_compact_oriented_singleLinkConditionalDensity_eq_of_agreeOffLink
    C A B target hAgree]
  simp

end
end MathlibAnalytic
end MGAP4D
