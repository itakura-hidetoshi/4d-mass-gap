import MGAP4D.MathlibAnalytic.PhysicalYangMillsSymmetryObservableConvergence

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Simultaneously transformed two-point expectations are invariant for the
continuum weak-limit law. -/
theorem physical_yang_mills_symmetry_twoPoint_expectation_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, O₁ (S.action g A) * O₂ (S.action g A)
      ∂(S.continuumMeasure : Measure S.Configuration)) =
      ∫ A, O₁ A * O₂ A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  simpa using
    physical_yang_mills_symmetry_bounded_observable_expectation_invariant
      S g (O₁ * O₂)

/-- Connected two-point correlations are invariant under every compatible
continuum symmetry inherited from the lattice approximations. -/
theorem physical_yang_mills_symmetry_connectedCorrelation_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, O₁ (S.action g A) * O₂ (S.action g A)
      ∂(S.continuumMeasure : Measure S.Configuration)) -
        (∫ A, O₁ (S.action g A)
          ∂(S.continuumMeasure : Measure S.Configuration)) *
        (∫ A, O₂ (S.action g A)
          ∂(S.continuumMeasure : Measure S.Configuration)) =
      (∫ A, O₁ A * O₂ A
        ∂(S.continuumMeasure : Measure S.Configuration)) -
        (∫ A, O₁ A
          ∂(S.continuumMeasure : Measure S.Configuration)) *
        (∫ A, O₂ A
          ∂(S.continuumMeasure : Measure S.Configuration)) := by
  rw [physical_yang_mills_symmetry_twoPoint_expectation_invariant S g O₁ O₂,
    physical_yang_mills_symmetry_bounded_observable_expectation_invariant S g O₁,
    physical_yang_mills_symmetry_bounded_observable_expectation_invariant S g O₂]

/-- Simultaneously transformed two-point expectations are invariant at every
embedded lattice approximation. -/
theorem physical_yang_mills_approximating_symmetry_twoPoint_expectation_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (g : S.Symmetry)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, O₁ (S.action g A) * O₂ (S.action g A)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ A, O₁ A * O₂ A
        ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  simpa using
    physical_yang_mills_approximating_symmetry_bounded_observable_expectation_invariant
      S n g (O₁ * O₂)

/-- Symmetry-transformed two-point expectations converge to the continuum
physical two-point expectation. -/
theorem physical_yang_mills_symmetry_transformed_twoPoint_expectation_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, O₁ (S.action g A) * O₂ (S.action g A)
          ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, O₁ A * O₂ A
          ∂(S.continuumMeasure : Measure S.Configuration))) := by
  simpa using
    physical_yang_mills_symmetry_transformed_bounded_observable_expectation_converges
      S g (O₁ * O₂)

/-- Symmetry-transformed connected two-point correlations converge to the
continuum connected correlation. -/
theorem physical_yang_mills_symmetry_transformed_connectedCorrelation_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    (O₁ O₂ : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ =>
        (∫ A, O₁ (S.action g A) * O₂ (S.action g A)
          ∂(S.approximatingMeasure n : Measure S.Configuration)) -
        (∫ A, O₁ (S.action g A)
          ∂(S.approximatingMeasure n : Measure S.Configuration)) *
        (∫ A, O₂ (S.action g A)
          ∂(S.approximatingMeasure n : Measure S.Configuration)))
      atTop
      (nhds
        ((∫ A, O₁ A * O₂ A
          ∂(S.continuumMeasure : Measure S.Configuration)) -
        (∫ A, O₁ A
          ∂(S.continuumMeasure : Measure S.Configuration)) *
        (∫ A, O₂ A
          ∂(S.continuumMeasure : Measure S.Configuration)))) := by
  have h₁₂ :=
    physical_yang_mills_symmetry_transformed_twoPoint_expectation_converges
      S g O₁ O₂
  have h₁ :=
    physical_yang_mills_symmetry_transformed_bounded_observable_expectation_converges
      S g O₁
  have h₂ :=
    physical_yang_mills_symmetry_transformed_bounded_observable_expectation_converges
      S g O₂
  exact h₁₂.sub (h₁.mul h₂)

end

end MathlibAnalytic
end MGAP4D
