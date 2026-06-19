import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantObservableRing
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

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

/-- A real linear functional equipped with pointwise positivity and unit
normalization on the gauge-invariant observable algebra. -/
structure PhysicalYangMillsGaugeInvariantPositiveFunctional
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) where
  toLinearMap :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →ₗ[ℝ] ℝ
  map_nonneg' :
    ∀ (O : physicalYangMillsGaugeInvariantObservableSubalgebra S),
      (∀ A, 0 ≤ (O : BoundedContinuousFunction S.Configuration ℝ) A) →
      0 ≤ toLinearMap O
  map_one' : toLinearMap 1 = 1

noncomputable def physicalYangMillsApproximatingGaugeInvariantPositiveFunctional
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    PhysicalYangMillsGaugeInvariantPositiveFunctional S where
  toLinearMap := physicalYangMillsApproximatingGaugeInvariantExpectation S n
  map_nonneg' O hO := integral_nonneg hO
  map_one' := by
    simp [physicalYangMillsApproximatingGaugeInvariantExpectation]

noncomputable def physicalYangMillsContinuumGaugeInvariantPositiveFunctional
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    PhysicalYangMillsGaugeInvariantPositiveFunctional S where
  toLinearMap := physicalYangMillsContinuumGaugeInvariantExpectation S
  map_nonneg' O hO := integral_nonneg hO
  map_one' := by
    simp [physicalYangMillsContinuumGaugeInvariantExpectation]

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
theorem physicalYangMillsApproximatingGaugeInvariantPositiveFunctional_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    (physicalYangMillsApproximatingGaugeInvariantPositiveFunctional S n).toLinearMap O =
      physicalYangMillsApproximatingGaugeInvariantExpectation S n O :=
  rfl

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantPositiveFunctional_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    (physicalYangMillsContinuumGaugeInvariantPositiveFunctional S).toLinearMap O =
      physicalYangMillsContinuumGaugeInvariantExpectation S O :=
  rfl

/-- Pointwise convergence of the lattice expectation linear maps. -/
theorem physical_yang_mills_gaugeInvariantExpectation_pointwise_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    Tendsto
      (fun n : ℕ =>
        physicalYangMillsApproximatingGaugeInvariantExpectation S n O)
      atTop
      (nhds (physicalYangMillsContinuumGaugeInvariantExpectation S O)) :=
  physical_yang_mills_gaugeInvariantObservable_expectation_converges S O

/-- Pointwise convergence of the normalized positive functional packages. -/
theorem physical_yang_mills_gaugeInvariantPositiveFunctional_pointwise_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    Tendsto
      (fun n : ℕ =>
        (physicalYangMillsApproximatingGaugeInvariantPositiveFunctional S n).toLinearMap O)
      atTop
      (nhds
        ((physicalYangMillsContinuumGaugeInvariantPositiveFunctional S).toLinearMap O)) :=
  physical_yang_mills_gaugeInvariantExpectation_pointwise_converges S O

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantExpectation_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    physicalYangMillsApproximatingGaugeInvariantExpectation S n 1 = 1 := by
  simp [physicalYangMillsApproximatingGaugeInvariantExpectation]

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantExpectation_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    physicalYangMillsContinuumGaugeInvariantExpectation S 1 = 1 := by
  simp [physicalYangMillsContinuumGaugeInvariantExpectation]

theorem physicalYangMillsApproximatingGaugeInvariantExpectation_nonneg
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S)
    (hO : ∀ A, 0 ≤ (O : BoundedContinuousFunction S.Configuration ℝ) A) :
    0 ≤ physicalYangMillsApproximatingGaugeInvariantExpectation S n O :=
  (physicalYangMillsApproximatingGaugeInvariantPositiveFunctional S n).map_nonneg' O hO

theorem physicalYangMillsContinuumGaugeInvariantExpectation_nonneg
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S)
    (hO : ∀ A, 0 ≤ (O : BoundedContinuousFunction S.Configuration ℝ) A) :
    0 ≤ physicalYangMillsContinuumGaugeInvariantExpectation S O :=
  (physicalYangMillsContinuumGaugeInvariantPositiveFunctional S).map_nonneg' O hO

end

end MathlibAnalytic
end MGAP4D
