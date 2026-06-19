import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantExpectationNormBound
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

private theorem physicalYangMillsApproximatingGaugeInvariantExpectation_continuous_bound
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    ‖physicalYangMillsApproximatingGaugeInvariantExpectation S n O‖ ≤
      (1 : ℝ) * ‖O‖ := by
  simpa only [one_mul] using
    physicalYangMillsApproximatingGaugeInvariantExpectation_norm_le S n O

private theorem physicalYangMillsContinuumGaugeInvariantExpectation_continuous_bound
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    ‖physicalYangMillsContinuumGaugeInvariantExpectation S O‖ ≤
      (1 : ℝ) * ‖O‖ := by
  simpa only [one_mul] using
    physicalYangMillsContinuumGaugeInvariantExpectation_norm_le S O

/-- The `n`-th embedded-lattice expectation as a continuous real-linear
functional on the physical gauge-invariant observable algebra. -/
noncomputable def physicalYangMillsApproximatingGaugeInvariantContinuousExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →L[ℝ] ℝ :=
  (physicalYangMillsApproximatingGaugeInvariantExpectation S n).mkContinuous
    1
    (physicalYangMillsApproximatingGaugeInvariantExpectation_continuous_bound S n)

/-- The continuum expectation as a continuous real-linear functional on the
physical gauge-invariant observable algebra. -/
noncomputable def physicalYangMillsContinuumGaugeInvariantContinuousExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →L[ℝ] ℝ :=
  (physicalYangMillsContinuumGaugeInvariantExpectation S).mkContinuous
    1
    (physicalYangMillsContinuumGaugeInvariantExpectation_continuous_bound S)

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantContinuousExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsApproximatingGaugeInvariantContinuousExpectation S n O =
      physicalYangMillsApproximatingGaugeInvariantExpectation S n O := by
  simp [physicalYangMillsApproximatingGaugeInvariantContinuousExpectation]

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantContinuousExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsContinuumGaugeInvariantContinuousExpectation S O =
      physicalYangMillsContinuumGaugeInvariantExpectation S O := by
  simp [physicalYangMillsContinuumGaugeInvariantContinuousExpectation]

/-- The continuous lattice expectation functionals converge pointwise to the
continuous continuum expectation functional. -/
theorem physical_yang_mills_gaugeInvariantContinuousExpectation_pointwise_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    Tendsto
      (fun n : ℕ =>
        physicalYangMillsApproximatingGaugeInvariantContinuousExpectation S n O)
      atTop
      (nhds
        (physicalYangMillsContinuumGaugeInvariantContinuousExpectation S O)) := by
  simpa using physical_yang_mills_gaugeInvariantExpectation_pointwise_converges S O

end

end MathlibAnalytic
end MGAP4D
