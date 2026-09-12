import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocality
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakLimitUniformlyVaryingObservable

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance physicalYangMillsEvenPeriodicWilsonOSUniformWeakLimitFromLocalitySideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalYangMillsEvenPeriodicWilsonOSUniformWeakLimitFromLocalityTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalYangMillsEvenPeriodicWilsonOSUniformWeakLimitFromLocalityCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalYangMillsEvenPeriodicWilsonOSUniformWeakLimitFromLocalitySecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalYangMillsEvenPeriodicWilsonOSUniformWeakLimitFromLocalityMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalYangMillsEvenPeriodicWilsonOSUniformWeakLimitFromLocalityBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A scale-dependent physical bounded-continuous observable is nonnegative at
its matching finite Wilson scale whenever its exact pullback is the reflected
product of one negative-half-independent full finite observable.

Unlike the fixed-test weak-limit bridge, this statement only asks for the
pullback identity at the single matching scale. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_varying_approximating_nonneg_of_negativeHalfIndependent
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ) (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (O : ℕ → BoundedContinuousFunction S.Configuration ℝ)
    (interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) = Measure.map (interpolate n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
          (beta n) (hbeta n)).gibbsMeasure)
    (f : ∀ n, BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge (halfExtent n) → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (hind : ∀ n, (periodicHypercubicEvenEdgeOrbitPartition
      (halfExtent n)).NegativeHalfIndependent (fun A => f n A))
    (quadraticObservable_pullback : ∀ n A, O n (interpolate n A) =
      f n A * f n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    (n : ℕ) :
    0 ≤ ∫ A, O n A ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  rw [approximatingMeasure_toMeasure_eq n]
  have heq :
      (∫ A, O n (interpolate n A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
          (beta n) (hbeta n)).gibbsMeasure) =
        ∫ A, f n A * f n
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
          (beta n) (hbeta n)).gibbsMeasure := by
    apply integral_congr_ae
    filter_upwards [] with A
    exact quadraticObservable_pullback n A
  calc
    0 ≤ ∫ A, O n (interpolate n A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
          (beta n) (hbeta n)).gibbsMeasure := by
      rw [heq]
      exact periodicHypercubicEvenWilsonGibbs_reflectionPositive_of_negativeHalfIndependent
        (halfExtent n) N hN (beta n) (hbeta n) (f n) (hind n)
    _ = ∫ A, O n A ∂Measure.map (interpolate n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
          (beta n) (hbeta n)).gibbsMeasure := by
      symm
      exact MeasureTheory.integral_map
        (interpolate_measurable n).aemeasurable
        (O n).continuous.aestronglyMeasurable

/-- Uniform convergence of scale-dependent physical OS quadratic observables
upgrades pointwise finite Wilson locality to continuum OS nonnegativity.

The finite observable may vary with the lattice scale.  The only cross-scale
analytic input is sup-norm convergence of the physical bounded-continuous
quadratic observables themselves. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_varying_continuum_nonneg_of_negativeHalfIndependent_of_uniform
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ) (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (O : ℕ → BoundedContinuousFunction S.Configuration ℝ)
    (Olim : BoundedContinuousFunction S.Configuration ℝ)
    (huniform : Tendsto (fun n => ‖O n - Olim‖) atTop (nhds 0))
    (interpolate : ∀ n, (PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) → S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) = Measure.map (interpolate n)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
          (beta n) (hbeta n)).gibbsMeasure)
    (f : ∀ n, BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge (halfExtent n) → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (hind : ∀ n, (periodicHypercubicEvenEdgeOrbitPartition
      (halfExtent n)).NegativeHalfIndependent (fun A => f n A))
    (quadraticObservable_pullback : ∀ n A, O n (interpolate n A) =
      f n A * f n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) :
    0 ≤ ∫ A, Olim A ∂(S.continuumMeasure : Measure S.Configuration) := by
  apply physical_yang_mills_bounded_observable_continuum_nonneg_of_uniform
    S O Olim huniform
  intro n
  exact physical_yang_mills_evenPeriodicWilsonOS_varying_approximating_nonneg_of_negativeHalfIndependent
    S halfExtent N hN beta hbeta O interpolate interpolate_measurable
    approximatingMeasure_toMeasure_eq f hind quadraticObservable_pullback n

end

end MathlibAnalytic
end MGAP4D
