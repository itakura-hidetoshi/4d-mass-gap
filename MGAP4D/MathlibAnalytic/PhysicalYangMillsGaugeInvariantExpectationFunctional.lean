import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantObservableRing
import Mathlib.Algebra.Order.Module.PositiveLinearMap
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

/-- The `n`-th embedded lattice expectation is a positive linear functional on
the physical gauge-invariant observable algebra. -/
noncomputable def physicalYangMillsApproximatingGaugeInvariantPositiveExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    (physicalYangMillsApproximatingGaugeInvariantExpectation S n)
    (by
      intro O hO
      exact integral_nonneg (fun A => hO A))

/-- The continuum expectation is a positive linear functional on the physical
gauge-invariant observable algebra. -/
noncomputable def physicalYangMillsContinuumGaugeInvariantPositiveExpectation
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    (physicalYangMillsContinuumGaugeInvariantExpectation S)
    (by
      intro O hO
      exact integral_nonneg (fun A => hO A))

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

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantPositiveExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsApproximatingGaugeInvariantPositiveExpectation S n O =
      physicalYangMillsApproximatingGaugeInvariantExpectation S n O :=
  rfl

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantPositiveExpectation_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    physicalYangMillsContinuumGaugeInvariantPositiveExpectation S O =
      physicalYangMillsContinuumGaugeInvariantExpectation S O :=
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

/-- The positive expectation functionals converge pointwise on every physical
 gauge-invariant observable. -/
theorem physical_yang_mills_gaugeInvariantPositiveExpectation_pointwise_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    Tendsto
      (fun n : ℕ =>
        physicalYangMillsApproximatingGaugeInvariantPositiveExpectation S n O)
      atTop
      (nhds
        (physicalYangMillsContinuumGaugeInvariantPositiveExpectation S O)) :=
  physical_yang_mills_gaugeInvariantExpectation_pointwise_converges S O

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

/-- Every approximating positive expectation functional is normalized. -/
@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantPositiveExpectation_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    physicalYangMillsApproximatingGaugeInvariantPositiveExpectation S n 1 = 1 := by
  simp

/-- The continuum positive expectation functional is normalized. -/
@[simp]
theorem physicalYangMillsContinuumGaugeInvariantPositiveExpectation_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsContinuumGaugeInvariantPositiveExpectation S 1 = 1 := by
  simp

end

end MathlibAnalytic
end MGAP4D
