import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData
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

/-- Integration against a cofinally indexed approximation is integration of its
pullback against the corresponding finite Gibbs law. -/
theorem
    PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData.approximatingExpectation_eq_gibbs_pullback
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ} {hBeta : 0 < beta} {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData
        S beta hBeta distance)
    (k : ℕ)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, O A ∂(S.approximatingMeasure k : Measure S.Configuration)) =
      ∫ U, O (B.interpolate k U)
        ∂(z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
          beta hBeta.le).gibbsMeasure := by
  rw [B.approximatingMeasure_eq_map k]
  exact MeasureTheory.integral_map
    (B.interpolate_measurable k).aemeasurable
    O.continuous.aestronglyMeasurable

end

end MathlibAnalytic
end MGAP4D
