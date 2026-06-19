import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantContinuousExpectation

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A normalized positive contractive continuous real-linear functional on the
physical gauge-invariant observable algebra. -/
structure PhysicalYangMillsGaugeInvariantContinuousState
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) where
  toContinuousLinearMap :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →L[ℝ] ℝ
  map_nonneg' :
    ∀ (O : physicalYangMillsGaugeInvariantObservableSubalgebra S),
      (∀ A, 0 ≤ (O : BoundedContinuousFunction S.Configuration ℝ) A) →
      0 ≤ toContinuousLinearMap O
  map_one' : toContinuousLinearMap 1 = 1
  map_norm_le' :
    ∀ (O : physicalYangMillsGaugeInvariantObservableSubalgebra S),
      ‖toContinuousLinearMap O‖ ≤
        ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖

/-- The `n`-th embedded-lattice expectation as a normalized positive
contractive continuous state. -/
noncomputable def physicalYangMillsApproximatingGaugeInvariantContinuousState
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    PhysicalYangMillsGaugeInvariantContinuousState S where
  toContinuousLinearMap :=
    physicalYangMillsApproximatingGaugeInvariantContinuousExpectation S n
  map_nonneg' O hO := by
    rw [physicalYangMillsApproximatingGaugeInvariantContinuousExpectation_apply]
    exact physicalYangMillsApproximatingGaugeInvariantExpectation_nonneg S n O hO
  map_one' := by
    rw [physicalYangMillsApproximatingGaugeInvariantContinuousExpectation_apply]
    exact physicalYangMillsApproximatingGaugeInvariantExpectation_one S n
  map_norm_le' O := by
    rw [physicalYangMillsApproximatingGaugeInvariantContinuousExpectation_apply]
    exact physicalYangMillsApproximatingGaugeInvariantExpectation_norm_le S n O

/-- The continuum expectation as a normalized positive contractive continuous
state. -/
noncomputable def physicalYangMillsContinuumGaugeInvariantContinuousState
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    PhysicalYangMillsGaugeInvariantContinuousState S where
  toContinuousLinearMap :=
    physicalYangMillsContinuumGaugeInvariantContinuousExpectation S
  map_nonneg' O hO := by
    rw [physicalYangMillsContinuumGaugeInvariantContinuousExpectation_apply]
    exact physicalYangMillsContinuumGaugeInvariantExpectation_nonneg S O hO
  map_one' := by
    rw [physicalYangMillsContinuumGaugeInvariantContinuousExpectation_apply]
    exact physicalYangMillsContinuumGaugeInvariantExpectation_one S
  map_norm_le' O := by
    rw [physicalYangMillsContinuumGaugeInvariantContinuousExpectation_apply]
    exact physicalYangMillsContinuumGaugeInvariantExpectation_norm_le S O

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantContinuousState_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).toContinuousLinearMap O =
      physicalYangMillsApproximatingGaugeInvariantExpectation S n O := by
  rfl

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantContinuousState_apply
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    (physicalYangMillsContinuumGaugeInvariantContinuousState S).toContinuousLinearMap O =
      physicalYangMillsContinuumGaugeInvariantExpectation S O := by
  rfl

@[simp]
theorem physicalYangMillsApproximatingGaugeInvariantContinuousState_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ) :
    (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).toContinuousLinearMap 1 = 1 :=
  (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).map_one'

@[simp]
theorem physicalYangMillsContinuumGaugeInvariantContinuousState_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    (physicalYangMillsContinuumGaugeInvariantContinuousState S).toContinuousLinearMap 1 = 1 :=
  (physicalYangMillsContinuumGaugeInvariantContinuousState S).map_one'

/-- Every embedded-lattice continuous state is positive on pointwise
nonnegative gauge-invariant observables. -/
theorem physicalYangMillsApproximatingGaugeInvariantContinuousState_nonneg
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S)
    (hO : ∀ A, 0 ≤ (O : BoundedContinuousFunction S.Configuration ℝ) A) :
    0 ≤ (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).
      toContinuousLinearMap O :=
  (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).map_nonneg' O hO

/-- The continuum continuous state is positive on pointwise nonnegative
physical gauge-invariant observables. -/
theorem physicalYangMillsContinuumGaugeInvariantContinuousState_nonneg
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S)
    (hO : ∀ A, 0 ≤ (O : BoundedContinuousFunction S.Configuration ℝ) A) :
    0 ≤ (physicalYangMillsContinuumGaugeInvariantContinuousState S).
      toContinuousLinearMap O :=
  (physicalYangMillsContinuumGaugeInvariantContinuousState S).map_nonneg' O hO

/-- Every embedded-lattice continuous state is contractive in the observable
uniform norm. -/
theorem physicalYangMillsApproximatingGaugeInvariantContinuousState_norm_le
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    ‖(physicalYangMillsApproximatingGaugeInvariantContinuousState S n).
        toContinuousLinearMap O‖ ≤
      ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖ :=
  (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).map_norm_le' O

/-- The continuum continuous state is contractive in the observable uniform
norm. -/
theorem physicalYangMillsContinuumGaugeInvariantContinuousState_norm_le
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    ‖(physicalYangMillsContinuumGaugeInvariantContinuousState S).
        toContinuousLinearMap O‖ ≤
      ‖(O : BoundedContinuousFunction S.Configuration ℝ)‖ :=
  (physicalYangMillsContinuumGaugeInvariantContinuousState S).map_norm_le' O

/-- The normalized positive contractive lattice states converge pointwise to
the continuum state. -/
theorem physical_yang_mills_gaugeInvariantContinuousState_pointwise_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    Tendsto
      (fun n : ℕ =>
        (physicalYangMillsApproximatingGaugeInvariantContinuousState S n).
          toContinuousLinearMap O)
      atTop
      (nhds
        ((physicalYangMillsContinuumGaugeInvariantContinuousState S).
          toContinuousLinearMap O)) := by
  simpa using
    physical_yang_mills_gaugeInvariantContinuousExpectation_pointwise_converges S O

end

end MathlibAnalytic
end MGAP4D
