import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantObservableRing
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Expectation against the `n`-th embedded lattice law, restricted to the real
algebra of pointwise gauge-invariant bounded continuous observables. -/
noncomputable def physicalYangMillsApproximatingGaugeInvariantExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →ₗ[ℝ] ℝ where
  toFun O :=
    ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
      ∂(S.approximatingMeasure n : Measure S.Configuration)
  map_add' O₁ O₂ := by
    simpa using integral_add'
      ((O₁ : BoundedContinuousFunction S.Configuration ℝ).integrable
        (S.approximatingMeasure n : Measure S.Configuration))
      ((O₂ : BoundedContinuousFunction S.Configuration ℝ).integrable
        (S.approximatingMeasure n : Measure S.Configuration))
  map_smul' c O := by
    simpa using integral_smul c
      (O : BoundedContinuousFunction S.Configuration ℝ)

/-- Continuum expectation restricted to the real algebra of pointwise
 gauge-invariant bounded continuous observables. -/
noncomputable def physicalYangMillsContinuumGaugeInvariantExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →ₗ[ℝ] ℝ where
  toFun O :=
    ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
      ∂(S.continuumMeasure : Measure S.Configuration)
  map_add' O₁ O₂ := by
    simpa using integral_add'
      ((O₁ : BoundedContinuousFunction S.Configuration ℝ).integrable
        (S.continuumMeasure : Measure S.Configuration))
      ((O₂ : BoundedContinuousFunction S.Configuration ℝ).integrable
        (S.continuumMeasure : Measure S.Configuration))
  map_smul' c O := by
    simpa using integral_smul c
      (O : BoundedContinuousFunction S.Configuration ℝ)

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsApproximatingGaugeInvariantExpectation S n O =
      ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
        ∂(S.approximatingMeasure n : Measure S.Configuration) :=
  rfl

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsContinuumGaugeInvariantExpectation S O =
      ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
        ∂(S.continuumMeasure : Measure S.Configuration) :=
  rfl

/-- The embedded-lattice expectation functionals converge pointwise on the
physical gauge-invariant observable algebra to the continuum expectation
functional. -/
theorem physical_yang_mills_gaugeInvariantExpectation_pointwise_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    Tendsto
      (fun n : ℕ =>
        physicalYangMillsApproximatingGaugeInvariantExpectation S n O)
      atTop
      (nhds (physicalYangMillsContinuumGaugeInvariantExpectation S O)) :=
  physical_yang_mills_gaugeInvariantObservable_expectation_converges S O

/-- Every approximating expectation functional is normalized on the constant
unit observable. -/
@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantExpectation_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    physicalYangMillsApproximatingGaugeInvariantExpectation S n 1 = 1 := by
  simp [physicalYangMillsApproximatingGaugeInvariantExpectation]

/-- The continuum expectation functional is normalized on the constant unit
observable. -/
@[simp]
theorem physicalYangMillsContinuumGaugeInvariantExpectation_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsContinuumGaugeInvariantExpectation S 1 = 1 := by
  simp [physicalYangMillsContinuumGaugeInvariantExpectation]

end

end MathlibAnalytic
end MGAP4D
