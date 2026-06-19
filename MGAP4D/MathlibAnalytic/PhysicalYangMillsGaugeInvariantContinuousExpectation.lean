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
  (physicalYangMillsApproximatingGaugeInvariantExpectation S n).mkContinuous 1
    (by
      intro O
      simpa using
        physicalYangMillsApproximatingGaugeInvariantExpectation_norm_le S n O)

/-- The continuum expectation as a continuous real-linear functional on the
physical gauge-invariant observable algebra. -/
noncomputable def physicalYangMillsContinuumGaugeInvariantContinuousExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →L[ℝ] ℝ :=
  (physicalYangMillsContinuumGaugeInvariantExpectation S).mkContinuous 1
    (by
      intro O
      simpa using
        physicalYangMillsContinuumGaugeInvariantExpectation_norm_le S O)

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantContinuousExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsApproximatingGaugeInvariantContinuousExpectation S n O =
      physicalYangMillsApproximatingGaugeInvariantExpectation S n O :=
  rfl

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantContinuousExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsContinuumGaugeInvariantContinuousExpectation S O =
      physicalYangMillsContinuumGaugeInvariantExpectation S O :=
  rfl

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
        (physicalYangMillsContinuumGaugeInvariantContinuousExpectation S O)) :=
  physical_yang_mills_gaugeInvariantExpectation_pointwise_converges S O

end

end MathlibAnalytic
end MGAP4D
