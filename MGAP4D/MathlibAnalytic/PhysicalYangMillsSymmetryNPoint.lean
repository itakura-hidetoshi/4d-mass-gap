import MGAP4D.MathlibAnalytic.PhysicalYangMillsSymmetryCorrelation
import Mathlib.Algebra.BigOperators.Pi

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Simultaneously transformed finite products of bounded continuous observables
have invariant continuum expectations. -/
theorem physical_yang_mills_symmetry_nPoint_expectation_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    {ι : Type} [DecidableEq ι]
    (s : Finset ι)
    (O : ι → BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, ∏ i in s, O i (S.action g A)
      ∂(S.continuumMeasure : Measure S.Configuration)) =
      ∫ A, ∏ i in s, O i A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  simpa using
    physical_yang_mills_symmetry_bounded_observable_expectation_invariant
      S g (∏ i in s, O i)

/-- Simultaneously transformed finite products have invariant expectations at
every embedded lattice approximation. -/
theorem physical_yang_mills_approximating_symmetry_nPoint_expectation_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (n : ℕ)
    (g : S.Symmetry)
    {ι : Type} [DecidableEq ι]
    (s : Finset ι)
    (O : ι → BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, ∏ i in s, O i (S.action g A)
      ∂(S.approximatingMeasure n : Measure S.Configuration)) =
      ∫ A, ∏ i in s, O i A
        ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  simpa using
    physical_yang_mills_approximating_symmetry_bounded_observable_expectation_invariant
      S n g (∏ i in s, O i)

/-- Symmetry-transformed finite n-point moments converge from the embedded
lattice laws to the continuum n-point moment. -/
theorem physical_yang_mills_symmetry_transformed_nPoint_expectation_converges
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    {ι : Type} [DecidableEq ι]
    (s : Finset ι)
    (O : ι → BoundedContinuousFunction S.Configuration ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, ∏ i in s, O i (S.action g A)
          ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, ∏ i in s, O i A
          ∂(S.continuumMeasure : Measure S.Configuration))) := by
  simpa using
    physical_yang_mills_symmetry_transformed_bounded_observable_expectation_converges
      S g (∏ i in s, O i)

end

end MathlibAnalytic
end MGAP4D
