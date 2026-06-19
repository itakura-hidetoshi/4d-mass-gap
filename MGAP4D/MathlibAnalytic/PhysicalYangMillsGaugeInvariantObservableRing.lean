import MGAP4D.MathlibAnalytic.PhysicalYangMillsSymmetryNPoint
import Mathlib.Algebra.Ring.Subring.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The bounded continuous observables fixed pointwise by every supplied
physical symmetry form a subring. -/
def physicalYangMillsGaugeInvariantObservableSubring
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) :
    Subring (BoundedContinuousFunction S.Configuration ℝ) where
  carrier := {O | ∀ g A, O (S.action g A) = O A}
  zero_mem' := by
    intro g A
    rfl
  one_mem' := by
    intro g A
    rfl
  add_mem' := by
    intro O₁ O₂ h₁ h₂ g A
    simp [h₁ g A, h₂ g A]
  neg_mem' := by
    intro O hO g A
    simp [hO g A]
  mul_mem' := by
    intro O₁ O₂ h₁ h₂ g A
    simp [h₁ g A, h₂ g A]

@[simp]
theorem mem_physicalYangMillsGaugeInvariantObservableSubring_iff
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    O ∈ physicalYangMillsGaugeInvariantObservableSubring S ↔
      ∀ g A, O (S.action g A) = O A :=
  Iff.rfl

/-- A gauge-invariant bounded continuous observable is pointwise unchanged by
the physical symmetry action. -/
theorem physical_yang_mills_gaugeInvariantObservable_action_eq
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubring S)
    (g : S.Symmetry)
    (A : S.Configuration) :
    (O : BoundedContinuousFunction S.Configuration ℝ) (S.action g A) =
      (O : BoundedContinuousFunction S.Configuration ℝ) A :=
  O.property g A

/-- Expectations of gauge-invariant bounded continuous observables converge
along the embedded lattice laws to their continuum expectations. -/
theorem physical_yang_mills_gaugeInvariantObservable_expectation_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubring S) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
          ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
          ∂(S.continuumMeasure : Measure S.Configuration))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    S.weakConvergence) (O : BoundedContinuousFunction S.Configuration ℝ)

/-- Symmetry-transformed expectations of a gauge-invariant observable coincide
pointwise with the untransformed expectations at every lattice scale. -/
theorem physical_yang_mills_gaugeInvariantObservable_approximating_expectation_eq
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubring S)
    (n : ℕ)
    (g : S.Symmetry) :
    (∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) (S.action g A)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
        ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  apply integral_congr_ae
  filter_upwards with A
  exact O.property g A

/-- The same pointwise fixedness identifies transformed and untransformed
continuum expectations. -/
theorem physical_yang_mills_gaugeInvariantObservable_continuum_expectation_eq
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (O : physicalYangMillsGaugeInvariantObservableSubring S)
    (g : S.Symmetry) :
    (∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) (S.action g A)
      ∂(S.continuumMeasure : Measure S.Configuration)) =
      ∫ A, (O : BoundedContinuousFunction S.Configuration ℝ) A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  apply integral_congr_ae
  filter_upwards with A
  exact O.property g A

end

end MathlibAnalytic
end MGAP4D
