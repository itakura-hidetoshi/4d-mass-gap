import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalResidualMassInfluence
import Mathlib.Tactic

/-!
# Weighted residual-measure domination from likelihood-ratio influence

The overlap-coupling spine previously used the sharp likelihood-ratio
coefficient only to control total unmatched mass. For the current positive-beta
L2 route we need the stronger statement that the same coefficient controls
arbitrary nonnegative energy weights carried by the left/right residual
densities.

The key point is elementary but structurally important:

  (p - min p q) + (q - min p q) = |p - q|

and the existing likelihood-ratio estimate gives

  |p - q| <= c(K) * (p + q),

where c(K) = (K - 1)/(K + 1).

After transport through ENNReal.ofReal, the sum of the exact left/right
residual densities is pointwise dominated by the same coefficient times the
sum of the two full conditional densities. Consequently every nonnegative
weighted lower integral satisfies the corresponding domination.

This removes the sup-norm bottleneck from the residual-mass step: later the
weight can be an actual squared centered section of a bounded-concrete
ground-state representative.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- The two real positive-part residuals sum exactly to the absolute density
difference. -/
theorem residual_pair_sum_eq_abs_sub
    (p q : ℝ) :
    (p - min p q) + (q - min p q) = |p - q| := by
  rcases le_total p q with hpq | hqp
  · rw [min_eq_left hpq, sub_self, abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring
  · rw [min_eq_right hqp, sub_self, abs_of_nonneg (sub_nonneg.mpr hqp)]
    ring

/-- Mutual likelihood-ratio domination controls the sum of the two
positive-part residual densities by the same sharp coefficient used for total
variation. -/
theorem residual_pair_sum_le_coefficient_mul_add
    (K p q : ℝ)
    (hK : 1 ≤ K)
    (hpq : p ≤ K * q)
    (hqp : q ≤ K * p) :
    (p - min p q) + (q - min p q) ≤
      coefficient K * (p + q) := by
  rw [residual_pair_sum_eq_abs_sub]
  exact abs_sub_le_coefficient_mul_add K p q hK hpq hqp

end HaarLikelihoodRatioInfluence

/-- The right unmatched ENNReal density is the ofReal image of the
corresponding positive-part real density. -/
theorem
    continuous_compact_oriented_singleLinkConditionalRightResidualDensity_eq_ofReal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalRightResidualDensity A B target g =
      ENNReal.ofReal
        (C.singleLinkConditionalDensityReal B target g -
          min (C.singleLinkConditionalDensityReal A target g)
            (C.singleLinkConditionalDensityReal B target g)) := by
  let p := C.singleLinkConditionalDensityReal A target g
  let q := C.singleLinkConditionalDensityReal B target g
  have hp : 0 ≤ p := by
    dsimp [p, ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal]
    exact div_nonneg (Real.exp_pos _).le
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target).le
  have hq : 0 ≤ q := by
    dsimp [q, ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal]
    exact div_nonneg (Real.exp_pos _).le
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C B target).le
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
  rw [continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real,
    continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real,
    ← ENNReal.ofReal_min]
  exact (ENNReal.ofReal_sub q (le_min hp hq)).symm

/-- Pointwise residual-density domination. The exact left/right unmatched
conditional densities are jointly bounded by the sharp likelihood-ratio
coefficient times the sum of the two full conditional densities. -/
theorem
    continuous_compact_oriented_singleLinkConditionalResidualDensity_sum_le_coefficient_mul_conditionalDensity_sum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          K * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          K * C.singleLinkConditionalDensityReal A target g)
    (g : C.base.Gauge) :
    C.singleLinkConditionalLeftResidualDensity A B target g +
        C.singleLinkConditionalRightResidualDensity A B target g ≤
      ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
        (C.singleLinkConditionalDensity target A g +
          C.singleLinkConditionalDensity target B g) := by
  let p := C.singleLinkConditionalDensityReal A target g
  let q := C.singleLinkConditionalDensityReal B target g
  have hp : 0 ≤ p := by
    dsimp [p, ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal]
    exact div_nonneg (Real.exp_pos _).le
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target).le
  have hq : 0 ≤ q := by
    dsimp [q, ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal]
    exact div_nonneg (Real.exp_pos _).le
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C B target).le
  have hLeft : 0 ≤ p - min p q := sub_nonneg.mpr (min_le_left _ _)
  have hRight : 0 ≤ q - min p q := sub_nonneg.mpr (min_le_right _ _)
  have hCoeff :
      0 ≤ HaarLikelihoodRatioInfluence.coefficient K := by
    unfold HaarLikelihoodRatioInfluence.coefficient
    exact div_nonneg (sub_nonneg.mpr hK) (by linarith)
  have hReal :
      (p - min p q) + (q - min p q) ≤
        HaarLikelihoodRatioInfluence.coefficient K * (p + q) := by
    exact
      HaarLikelihoodRatioInfluence.residual_pair_sum_le_coefficient_mul_add
        K p q hK (hRatio g).1 (hRatio g).2
  rw [
    continuous_compact_oriented_singleLinkConditionalLeftResidualDensity_eq_ofReal,
    continuous_compact_oriented_singleLinkConditionalRightResidualDensity_eq_ofReal]
  change
    ENNReal.ofReal (p - min p q) + ENNReal.ofReal (q - min p q) ≤
      ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
        (C.singleLinkConditionalDensity target A g +
          C.singleLinkConditionalDensity target B g)
  rw [← ENNReal.ofReal_add hLeft hRight]
  calc
    ENNReal.ofReal ((p - min p q) + (q - min p q)) ≤
        ENNReal.ofReal
          (HaarLikelihoodRatioInfluence.coefficient K * (p + q)) :=
      ENNReal.ofReal_le_ofReal hReal
    _ =
        ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
          ENNReal.ofReal (p + q) := by
      rw [ENNReal.ofReal_mul hCoeff]
    _ =
        ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
          (ENNReal.ofReal p + ENNReal.ofReal q) := by
      rw [ENNReal.ofReal_add hp hq]
    _ =
        ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
          (C.singleLinkConditionalDensity target A g +
            C.singleLinkConditionalDensity target B g) := by
      rw [
        ← continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real
          C A target g,
        ← continuous_compact_oriented_singleLinkConditionalDensity_eq_ofReal_real
          C B target g]

/-- Weighted-energy form of the preceding pointwise domination. No boundedness
or integrability hypothesis is imposed on weight; the statement lives in
ENNReal and follows by monotonicity of the lower integral.

Taking weight g = ofReal ((X g - c)^2) is the intended RMS application. -/
theorem
    continuous_compact_oriented_singleLinkConditionalResidualDensity_weighted_lintegral_le_coefficient
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          K * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          K * C.singleLinkConditionalDensityReal A target g)
    (weight : C.base.Gauge → ℝ≥0∞) :
    (∫⁻ g,
      weight g *
        (C.singleLinkConditionalLeftResidualDensity A B target g +
          C.singleLinkConditionalRightResidualDensity A B target g)
      ∂normalizedCompactHaar C.base.Gauge) ≤
    ∫⁻ g,
      weight g *
        (ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
          (C.singleLinkConditionalDensity target A g +
            C.singleLinkConditionalDensity target B g))
      ∂normalizedCompactHaar C.base.Gauge := by
  apply lintegral_mono
  intro g
  exact mul_le_mul_left'
    (continuous_compact_oriented_singleLinkConditionalResidualDensity_sum_le_coefficient_mul_conditionalDensity_sum
      C A B target K hK hRatio g)
    (weight g)

end

end MGAP4D.MathlibAnalytic
