import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalTV
import MGAP4D.MathlibAnalytic.ContinuousProbabilityDensityLikelihoodRatioTV

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Mutual pointwise exponential likelihood-ratio control gives the sharp
compact-Haar total-variation bound. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_mutual_exp_ratio
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hAB : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensity A target g ≤
        Real.exp R * C.singleLinkConditionalDensity B target g)
    (hBA : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensity B target g ≤
        Real.exp R * C.singleLinkConditionalDensity A target g) :
    C.singleLinkConditionalTotalVariation A B target ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
  exact continuous_probabilityDensity_totalVariation_le_of_mutual_le_mul
    (normalizedCompactHaar C.base.Gauge)
    (C.singleLinkConditionalDensity A target)
    (C.singleLinkConditionalDensity B target)
    (continuous_compact_oriented_singleLinkConditionalDensity C A target)
    (continuous_compact_oriented_singleLinkConditionalDensity C B target)
    (continuous_compact_oriented_integral_singleLinkConditionalDensity C A target)
    (continuous_compact_oriented_integral_singleLinkConditionalDensity C B target)
    (Real.exp R) (Real.one_le_exp hR)
    (fun g => le_of_lt
      (continuous_compact_oriented_singleLinkConditionalDensity_pos C A target g))
    (fun g => le_of_lt
      (continuous_compact_oriented_singleLinkConditionalDensity_pos C B target g))
    hAB hBA

end
end MathlibAnalytic
end MGAP4D
