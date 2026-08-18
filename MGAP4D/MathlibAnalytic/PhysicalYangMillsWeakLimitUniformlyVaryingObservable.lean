import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakMeasureLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Weak convergence of the physical probability measures remains valid when
the bounded-continuous test observable itself varies with the lattice scale,
provided that the varying observables converge in sup norm to one fixed
continuum observable.

This is the uniform triangular-array form needed to use scale-dependent
cylinder realizations without pretending that their physical observables are
literally identical at every lattice scale. -/
theorem physical_yang_mills_bounded_observable_expectation_converges_of_uniform
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : ℕ → BoundedContinuousFunction S.Configuration ℝ)
    (Olim : BoundedContinuousFunction S.Configuration ℝ)
    (huniform : Tendsto (fun n => ‖O n - Olim‖) atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        ∫ A, O n A ∂(S.approximatingMeasure n : Measure S.Configuration))
      atTop
      (nhds
        (∫ A, Olim A ∂(S.continuumMeasure : Measure S.Configuration))) := by
  have herrorBound (n : ℕ) :
      ‖∫ A, O n A - Olim A
          ∂(S.approximatingMeasure n : Measure S.Configuration)‖ ≤
        ‖O n - Olim‖ := by
    have h := norm_integral_le_of_norm_le_const
      (μ := (S.approximatingMeasure n : Measure S.Configuration))
      (C := ‖O n - Olim‖)
      (f := fun A => O n A - Olim A)
      (ae_of_all _ fun A => by
        simpa using (O n - Olim).norm_coe_le_norm A)
    simpa using h
  have herror :
      Tendsto
        (fun n : ℕ =>
          ∫ A, O n A - Olim A
            ∂(S.approximatingMeasure n : Measure S.Configuration))
        atTop (nhds 0) :=
    squeeze_zero_norm herrorBound huniform
  have hfixed := physical_yang_mills_bounded_observable_expectation_converges S Olim
  convert herror.add hfixed using 1
  · funext n
    rw [integral_sub]
    · ring
    · exact BoundedContinuousFunction.integrable _ (O n)
    · exact BoundedContinuousFunction.integrable _ Olim
  · simp

/-- Nonnegativity of uniformly convergent scale-dependent bounded-continuous
expectations passes to the physical continuum weak limit.

In particular, finite Wilson OS positivity may be proved for a sequence of
scale-dependent cylinder observables and transported to one fixed continuum
observable once their quadratic observables converge in sup norm. -/
theorem physical_yang_mills_bounded_observable_continuum_nonneg_of_uniform
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (O : ℕ → BoundedContinuousFunction S.Configuration ℝ)
    (Olim : BoundedContinuousFunction S.Configuration ℝ)
    (huniform : Tendsto (fun n => ‖O n - Olim‖) atTop (nhds 0))
    (hnonneg : ∀ n,
      0 ≤ ∫ A, O n A
        ∂(S.approximatingMeasure n : Measure S.Configuration)) :
    0 ≤ ∫ A, Olim A ∂(S.continuumMeasure : Measure S.Configuration) := by
  exact ge_of_tendsto
    (physical_yang_mills_bounded_observable_expectation_converges_of_uniform
      S O Olim huniform)
    (Eventually.of_forall hnonneg)

end

end MathlibAnalytic
end MGAP4D
