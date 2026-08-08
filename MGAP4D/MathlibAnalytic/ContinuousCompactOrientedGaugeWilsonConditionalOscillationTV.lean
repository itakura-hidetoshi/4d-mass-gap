import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalTVBound
import MGAP4D.MathlibAnalytic.ContinuousNormalizedExponentialOscillation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Oscillation bound for the difference of two compact one-link conditional
Gibbs exponents. -/
def ContinuousCompactOrientedGaugeWilsonSystem.SingleLinkExponentDifferenceOscillationBound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ) : Prop :=
  ∀ u v : C.base.Gauge,
    ((C.singleLinkGibbsExponent A target u -
        C.singleLinkGibbsExponent B target u) -
      (C.singleLinkGibbsExponent A target v -
        C.singleLinkGibbsExponent B target v)) ≤ R

/-- The explicit compact conditional density is the normalized continuous
exponential density of the one-link Gibbs exponent. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_eq_continuousNormalizedExp
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalDensity A target =
      continuousNormalizedExp
        (normalizedCompactHaar C.base.Gauge)
        (C.singleLinkGibbsExponent A target) := by
  rfl

/-- Exponent-difference oscillation gives mutual pointwise exponential control
of the exact compact conditional densities. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_exp_mul_of_oscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hOsc : C.SingleLinkExponentDifferenceOscillationBound A B target R)
    (g : C.base.Gauge) :
    C.singleLinkConditionalDensity A target g ≤
        Real.exp R * C.singleLinkConditionalDensity B target g ∧
      C.singleLinkConditionalDensity B target g ≤
        Real.exp R * C.singleLinkConditionalDensity A target g := by
  rw [continuous_compact_oriented_singleLinkConditionalDensity_eq_continuousNormalizedExp,
    continuous_compact_oriented_singleLinkConditionalDensity_eq_continuousNormalizedExp]
  exact continuousNormalizedExp_mutual_le_exp_mul_of_difference_oscillation
    (normalizedCompactHaar C.base.Gauge)
    (C.singleLinkGibbsExponent A target)
    (C.singleLinkGibbsExponent B target)
    (continuous_compact_oriented_singleLinkGibbsExponent C A target)
    (continuous_compact_oriented_singleLinkGibbsExponent C B target)
    R hOsc g

/-- Exponent-difference oscillation gives the sharp compact conditional
Haar--Gibbs total-variation estimate. -/
theorem continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_exponentDifferenceOscillation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc : C.SingleLinkExponentDifferenceOscillationBound A B target R) :
    C.singleLinkConditionalTotalVariation A B target ≤
      (Real.exp R - 1) / (Real.exp R + 1) := by
  apply continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_mutual_exp_ratio
    C A B target R hR
  · intro g
    exact
      (continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_exp_mul_of_oscillation
        C A B target R hOsc g).1
  · intro g
    exact
      (continuous_compact_oriented_singleLinkConditionalDensity_mutual_le_exp_mul_of_oscillation
        C A B target R hOsc g).2

end
end MathlibAnalytic
end MGAP4D
