import MGAP4D.MathlibAnalytic.PhysicalYangMillsSymmetryObservable

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Function

noncomputable section

/-- Measure-level symmetry invariance for every embedded lattice approximation. -/
theorem physical_yang_mills_approximating_symmetry_toMeasure_map_eq_self
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (g : S.Symmetry) :
    Measure.map (S.action g)
        (S.approximatingMeasure n : Measure S.Configuration) =
      (S.approximatingMeasure n : Measure S.Configuration) := by
  have h := congrArg ProbabilityMeasure.toMeasure
    (S.approximatingInvariant n g)
  simpa only [ProbabilityMeasure.toMeasure_map] using h

/-- Every measurable observable has the same pushforward law before and after a
compatible symmetry transformation at every lattice approximation. -/
theorem physical_yang_mills_approximating_symmetry_observable_law_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (g : S.Symmetry)
    {Y : Type} [MeasurableSpace Y]
    (O : S.Configuration → Y)
    (hO : Measurable O) :
    Measure.map (O ∘ S.action g)
        (S.approximatingMeasure n : Measure S.Configuration) =
      Measure.map O
        (S.approximatingMeasure n : Measure S.Configuration) := by
  calc
    Measure.map (O ∘ S.action g)
        (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map O
          (Measure.map (S.action g)
            (S.approximatingMeasure n : Measure S.Configuration)) :=
      (Measure.map_map hO (S.action_continuous g).measurable).symm
    _ = Measure.map O
          (S.approximatingMeasure n : Measure S.Configuration) := by
      rw [physical_yang_mills_approximating_symmetry_toMeasure_map_eq_self]

/-- Expectations of bounded continuous observables are symmetry invariant at
every embedded lattice approximation. -/
theorem physical_yang_mills_approximating_symmetry_bounded_observable_expectation_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (g : S.Symmetry)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, O (S.action g A)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ A, O A
        ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  calc
    (∫ A, O (S.action g A)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
        ∫ A, O A
          ∂Measure.map (S.action g)
            (S.approximatingMeasure n : Measure S.Configuration) := by
      symm
      exact MeasureTheory.integral_map
        (S.action_continuous g).measurable.aemeasurable
        O.continuous.aestronglyMeasurable
    _ = ∫ A, O A
          ∂(S.approximatingMeasure n : Measure S.Configuration) := by
      rw [physical_yang_mills_approximating_symmetry_toMeasure_map_eq_self]

/-- Symmetry-transformed bounded continuous observables along the lattice
approximations converge to the same continuum expectation. -/
theorem physical_yang_mills_symmetry_transformed_bounded_observable_expectation_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, O (S.action g A)
          ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, O A
          ∂(S.continuumMeasure : Measure S.Configuration))) := by
  have hSequence :
      (fun n : ℕ =>
        ∫ A, O (S.action g A)
          ∂(S.approximatingMeasure n : Measure S.Configuration)) =
        (fun n : ℕ =>
          ∫ A, O A
            ∂(S.approximatingMeasure n : Measure S.Configuration)) := by
    funext n
    exact
      physical_yang_mills_approximating_symmetry_bounded_observable_expectation_invariant
        S n g O
  rw [hSequence]
  exact
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      S.weakConvergence) O

end

end MathlibAnalytic
end MGAP4D
