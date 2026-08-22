import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanGibbsCovarianceRemainderContraction
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanSpectralEnclosureL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Vanishing of the random-scan Gibbs covariance remainder

The finite remainder estimate has the form

`|Cov(F,R^M O)| <= ||F|| * (q^M * Tot(delta(O)))`.

For a nonnegative Dobrushin coefficient and a nonempty physical-link set, the
normalized random-scan rate `q` is nonnegative.  Strict Dobrushin contraction
also gives `q < 1`, so the geometric envelope tends to zero.  Squeezing the
absolute covariance by that envelope yields

`Cov(F,R^M O) -> 0`.

This is still a finite-volume statement about the auxiliary random-scan
iteration.  Spatial clustering is not asserted in this file; it is obtained
only after this limit is combined with the separated-support partial telescope.
No continuum or Hamiltonian mass-gap conclusion is made here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Under strict Dobrushin contraction, the actual bounded-continuous
random-scan covariance remainder tends to zero. -/
theorem
    continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_iterate_tendsto_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hCoefficientNonneg : 0 ≤ D.coefficient)
    (hCoefficientLtOne : D.coefficient < 1)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    Tendsto
      (fun M : ℕ =>
        C.gibbsCovarianceReal (fun A => F A)
          (fun A =>
            ((P.toRandomScanCenteredState).randomScanIterate D M).observable A))
      atTop (nhds 0) := by
  let q : ℝ :=
    continuousCompactOrientedDobrushinRandomScanRate C D.coefficient
  let total : ℝ :=
    continuousCompactOrientedGaugeWilsonTotalVariation P.variation
  have hRateNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      continuous_compact_oriented_dobrushinRandomScanRate_nonneg
        C D.coefficient hCoefficientNonneg hEdge
  have hRateLtOne : q < 1 := by
    dsimp [q]
    exact
      continuous_compact_oriented_dobrushinRandomScanRate_lt_one
        C D.coefficient hCoefficientLtOne hEdge
  have hPow : Tendsto (fun M : ℕ => q ^ M) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hRateNonneg hRateLtOne
  have hEnvelope :
      Tendsto (fun M : ℕ => ‖F‖ * (q ^ M * total)) atTop (nhds 0) := by
    have hRight :
        Tendsto (fun M : ℕ => q ^ M * total) atTop (nhds 0) := by
      simpa using hPow.mul_const total
    simpa using tendsto_const_nhds.mul hRight
  have hBound (M : ℕ) :
      |C.gibbsCovarianceReal (fun A => F A)
          (fun A =>
            ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)| ≤
        ‖F‖ * (q ^ M * total) := by
    simpa [q, total] using
      continuous_compact_oriented_gibbsCovarianceReal_randomScanCenteredState_iterate_abs_le_norm_mul_pow_rate_mul_totalVariation
        C F O P D hEdge hRateNonneg M
  have hAbs :
      Tendsto
        (fun M : ℕ =>
          |C.gibbsCovarianceReal (fun A => F A)
            (fun A =>
              ((P.toRandomScanCenteredState).randomScanIterate D M).observable A)|)
        atTop (nhds 0) := by
    exact squeeze_zero'
      (eventually_of_forall fun M => abs_nonneg _)
      (eventually_of_forall hBound)
      hEnvelope
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa [Real.norm_eq_abs] using hAbs

end

end MathlibAnalytic
end MGAP4D
