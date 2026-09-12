import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCofinalPlaquetteExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance (index : ℕ → ℕ) (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k)) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- A pointwise pullback identity converts the common-space expectation into the
corresponding finite Gibbs expectation. -/
theorem
    PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData.approximatingExpectation_eq_gibbs_of_pullback
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ} {hBeta : 0 < beta} {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData
        S beta hBeta distance)
    (k : ℕ)
    (O : BoundedContinuousFunction S.Configuration ℝ)
    (f :
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
        beta hBeta.le).Configuration → ℝ)
    (hPull : ∀ U, O (B.interpolate k U) = f U) :
    (∫ A, O A ∂(S.approximatingMeasure k : Measure S.Configuration)) =
      ∫ U, f U
        ∂(z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
          beta hBeta.le).gibbsMeasure := by
  rw [B.approximatingExpectation_eq_gibbs_pullback k O]
  apply integral_congr_ae
  filter_upwards [] with U
  exact hPull U

end

end MathlibAnalytic
end MGAP4D
