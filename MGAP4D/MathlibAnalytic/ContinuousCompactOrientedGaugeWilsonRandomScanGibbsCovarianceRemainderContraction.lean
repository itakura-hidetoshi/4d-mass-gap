import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonGibbsCovarianceLinkVariation
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanCenteredIteration
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanTotalIterateContraction
import Mathlib.Tactic

/-!
# Finite geometric contraction of the random-scan Gibbs covariance remainder

The actual bounded-continuous random-scan iterate carries exactly the abstract
Dobrushin variation iterate.  Combining that identification with finite
power contraction of total variation gives

`Tot(delta(R^M O)) <= q^M Tot(delta(O))`.

The canonical global covariance/variation comparison then yields the finite
remainder estimate

`|Cov(F,R^M O)| <= ||F|| * (q^M * Tot(delta(O)))`.

This file is deliberately finite in `M`.  It does not yet use `q < 1`, take a
limit, remove the covariance remainder, assert absolute spatial clustering,
or make any continuum or Hamiltonian mass-gap conclusion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The centered variation profile carried by the actual `M`-step Feller
random-scan observable inherits the finite power contraction of the abstract
variation iterate. -/
theorem
    continuous_compact_oriented_randomScanCenteredState_iterate_totalVariation_le_pow_rate_mul
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (hRateNonneg :
      0 ≤ continuousCompactOrientedDobrushinRandomScanRate C D.coefficient)
    (M : ℕ) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        ((P.toRandomScanCenteredState).randomScanIterate D M).profile.variation ≤
      (continuousCompactOrientedDobrushinRandomScanRate C D.coefficient) ^ M *
        continuousCompactOrientedGaugeWilsonTotalVariation P.variation := by
  rw [continuous_compact_oriented_randomScanCenteredState_iterate_variation_eq]
  exact
    continuous_compact_oriented_dobrushinRandomScanVariationIterate_total_le_pow_rate_mul
      D P.variation P.variation_nonneg hEdge hRateNonneg M

/-- The actual finite random-scan covariance remainder contracts at the same
Dobrushin power rate as the total centered variation of its right observable. -/
theorem
    continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_iterate_abs_le_norm_mul_pow_rate_mul_totalVariation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (hRateNonneg :
      0 ≤ continuousCompactOrientedDobrushinRandomScanRate C D.coefficient)
    (M : ℕ) :
    |C.gibbsCovarianceReal (fun A => F A)
        (fun A =>
          ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)| ≤
      ‖F‖ *
        ((continuousCompactOrientedDobrushinRandomScanRate C D.coefficient) ^ M *
          continuousCompactOrientedGaugeWilsonTotalVariation P.variation) := by
  have hCov :=
    continuous_compact_oriented_gibbsCovarianceReal_abs_le_norm_mul_sum_centeredVariation
      C F ((P.toRandomScanCenteredState).randomScanIterate D M).observable
        ((P.toRandomScanCenteredState).randomScanIterate D M).profile
  have hTotal :=
    continuous_compact_oriented_randomScanCenteredState_iterate_totalVariation_le_pow_rate_mul
      P D hEdge hRateNonneg M
  calc
    |C.gibbsCovarianceReal (fun A => F A)
        (fun A =>
          ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)| ≤
      ‖F‖ * ∑ e : C.base.geometry.Edge,
        ((P.toRandomScanCenteredState).randomScanIterate D M).profile.variation e := hCov
    _ = ‖F‖ *
        continuousCompactOrientedGaugeWilsonTotalVariation
          ((P.toRandomScanCenteredState).randomScanIterate D M).profile.variation := by
      rfl
    _ ≤ ‖F‖ *
        ((continuousCompactOrientedDobrushinRandomScanRate C D.coefficient) ^ M *
          continuousCompactOrientedGaugeWilsonTotalVariation P.variation) :=
      mul_le_mul_of_nonneg_left hTotal (norm_nonneg F)

end

end MathlibAnalytic
end MGAP4D
