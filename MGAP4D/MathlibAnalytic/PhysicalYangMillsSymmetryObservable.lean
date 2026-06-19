import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakMeasureLimit
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function

noncomputable section

/-- Measure-level form of continuum symmetry invariance. -/
theorem physical_yang_mills_symmetry_toMeasure_map_eq_self
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry) :
    Measure.map (S.action g)
        (S.continuumMeasure : Measure S.Configuration) =
      (S.continuumMeasure : Measure S.Configuration) := by
  have h := congrArg ProbabilityMeasure.toMeasure
    (physical_yang_mills_symmetry_passes_to_weak_limit S g)
  simpa only [ProbabilityMeasure.toMeasure_map] using h

/-- Every measurable physical observable has the same continuum pushforward law
before and after a compatible symmetry transformation. -/
theorem physical_yang_mills_symmetry_observable_law_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    {Y : Type} [MeasurableSpace Y]
    (O : S.Configuration → Y)
    (hO : Measurable O) :
    Measure.map (O ∘ S.action g)
        (S.continuumMeasure : Measure S.Configuration) =
      Measure.map O
        (S.continuumMeasure : Measure S.Configuration) := by
  calc
    Measure.map (O ∘ S.action g)
        (S.continuumMeasure : Measure S.Configuration) =
        Measure.map O
          (Measure.map (S.action g)
            (S.continuumMeasure : Measure S.Configuration)) :=
      (Measure.map_map hO (S.action_continuous g).measurable).symm
    _ = Measure.map O
          (S.continuumMeasure : Measure S.Configuration) := by
      rw [physical_yang_mills_symmetry_toMeasure_map_eq_self]

/-- Expectations of bounded continuous physical observables are invariant under
all compatible continuum symmetries inherited from the lattice approximations. -/
theorem physical_yang_mills_symmetry_bounded_observable_expectation_invariant
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (g : S.Symmetry)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, O (S.action g A)
      ∂(S.continuumMeasure : Measure S.Configuration)) =
      ∫ A, O A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  calc
    (∫ A, O (S.action g A)
      ∂(S.continuumMeasure : Measure S.Configuration)) =
        ∫ A, O A
          ∂Measure.map (S.action g)
            (S.continuumMeasure : Measure S.Configuration) := by
      symm
      exact MeasureTheory.integral_map
        (S.action_continuous g).measurable.aemeasurable
        O.continuous.aestronglyMeasurable
    _ = ∫ A, O A
          ∂(S.continuumMeasure : Measure S.Configuration) := by
      rw [physical_yang_mills_symmetry_toMeasure_map_eq_self]

end

end MathlibAnalytic
end MGAP4D
