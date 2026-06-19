import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantExpectationFunctional

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Every embedded-lattice gauge-invariant expectation is bounded by the
uniform norm of the observable. -/
theorem physicalYangMillsApproximatingGaugeInvariantExpectation_norm_le
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    ‖physicalYangMillsApproximatingGaugeInvariantExpectation S n O‖ ≤
      ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖ := by
  simpa [physicalYangMillsApproximatingGaugeInvariantExpectation] using
    (O : BoundedContinuousFunction S.Configuration ℝ).norm_integral_le_norm
      (S.approximatingMeasure n : Measure S.Configuration)

/-- The continuum gauge-invariant expectation is bounded by the uniform norm of
its observable. -/
theorem physicalYangMillsContinuumGaugeInvariantExpectation_norm_le
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    ‖physicalYangMillsContinuumGaugeInvariantExpectation S O‖ ≤
      ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖ := by
  simpa [physicalYangMillsContinuumGaugeInvariantExpectation] using
    (O : BoundedContinuousFunction S.Configuration ℝ).norm_integral_le_norm
      (S.continuumMeasure : Measure S.Configuration)

/-- The whole sequence of embedded-lattice expectation values is uniformly
bounded by the observable norm. -/
theorem physicalYangMillsApproximatingGaugeInvariantExpectation_uniform_norm_le
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    ∀ n : ℕ,
      ‖physicalYangMillsApproximatingGaugeInvariantExpectation S n O‖ ≤
        ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖ :=
  fun n => physicalYangMillsApproximatingGaugeInvariantExpectation_norm_le S n O

end

end MathlibAnalytic
end MGAP4D
