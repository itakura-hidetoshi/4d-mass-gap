import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantExpectationNormBound
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- The `n`-th embedded-lattice expectation as a continuous real-linear
functional on the physical gauge-invariant observable algebra. -/
noncomputable def physicalYangMillsApproximatingGaugeInvariantContinuousExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (physicalYangMillsApproximatingGaugeInvariantExpectation S n :
      physicalYangMillsGaugeInvariantObservableSubalgebra S →ₗ[ℝ] ℝ)
    1
    (by
      intro O
      rw [one_mul]
      change
        ‖physicalYangMillsApproximatingGaugeInvariantExpectation S n O‖ ≤
          ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖
      exact physicalYangMillsApproximatingGaugeInvariantExpectation_norm_le S n O)

/-- The continuum expectation as a continuous real-linear functional on the
physical gauge-invariant observable algebra. -/
noncomputable def physicalYangMillsContinuumGaugeInvariantContinuousExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (physicalYangMillsContinuumGaugeInvariantExpectation S :
      physicalYangMillsGaugeInvariantObservableSubalgebra S →ₗ[ℝ] ℝ)
    1
    (by
      intro O
      rw [one_mul]
      change
        ‖physicalYangMillsContinuumGaugeInvariantExpectation S O‖ ≤
          ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖
      exact physicalYangMillsContinuumGaugeInvariantExpectation_norm_le S O)

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
