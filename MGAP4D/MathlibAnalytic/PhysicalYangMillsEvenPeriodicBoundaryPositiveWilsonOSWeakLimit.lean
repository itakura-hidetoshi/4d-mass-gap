import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionPositivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSWeakLimit

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Concrete identification data connecting a fixed bounded continuous physical
Osterwalder--Schrader quadratic observable to the actual finite-volume
even-periodic `SU(N)` Wilson Gibbs reflection forms when the finite positive-time
observable may depend on both the reflection-fixed boundary and the positive
open half.

Compared with `PhysicalYangMillsEvenPeriodicWilsonOSWeakLimitBridge`, this
bridge admits the natural time-zero boundary dependence required by positive-time
cylinders.  The finite-volume positivity theorem is still theorem-generated;
no reflection-positivity premise is stored in the bridge. -/
structure PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : BoundedContinuousFunction S.Configuration ℝ) where
  interpolate :
    ∀ n,
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        S.Configuration
  interpolate_measurable : ∀ n, Measurable (interpolate n)
  boundaryPositiveObservable :
    ∀ n, BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration
        (halfExtent n) N) ℝ
  approximatingMeasure_toMeasure_eq :
    ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map (interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure
  quadraticObservable_pullback :
    ∀ n A,
      Q (interpolate n A) =
        periodicHypercubicEvenBoundaryPositiveFullReflectedObservable
          (halfExtent n) (boundaryPositiveObservable n) A

/-- The boundary-positive finite-volume Wilson Gibbs theorem makes every
physical approximating expectation in the strengthened bridge nonnegative. -/
theorem physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_nonneg
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : BoundedContinuousFunction S.Configuration ℝ)
    (B : PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge
      S halfExtent N hN beta hbeta Q)
    (n : ℕ) :
    0 ≤ ∫ A, Q A
      ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  rw [B.approximatingMeasure_toMeasure_eq n]
  have heq :
      (∫ A, Q (B.interpolate n A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure) =
        ∫ A,
          periodicHypercubicEvenBoundaryPositiveFullReflectedObservable
            (halfExtent n) (B.boundaryPositiveObservable n) A
          ∂(periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure := by
    apply integral_congr_ae
    filter_upwards [] with A
    exact B.quadraticObservable_pullback n A
  calc
    0 ≤ ∫ A, Q (B.interpolate n A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsMeasure := by
      rw [heq]
      exact
        periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectionPositive_boundedContinuous
          (halfExtent n) N hN (beta n) (hbeta n)
          (B.boundaryPositiveObservable n)
    _ = ∫ A, Q A
        ∂Measure.map (B.interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure := by
      symm
      exact MeasureTheory.integral_map
        (B.interpolate_measurable n).aemeasurable
        Q.continuous.aestronglyMeasurable

/-- Boundary-positive finite-volume Wilson Gibbs reflection positivity passes
to the physical continuum weak limit for every fixed bounded continuous
physical quadratic observable equipped with the strengthened pullback bridge. -/
theorem physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_continuum_nonneg
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : BoundedContinuousFunction S.Configuration ℝ)
    (B : PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge
      S halfExtent N hN beta hbeta Q) :
    0 ≤ ∫ A, Q A
      ∂(S.continuumMeasure : Measure S.Configuration) := by
  exact physical_yang_mills_bounded_observable_nonneg_of_approximating
    S Q
    (fun n =>
      physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_nonneg
        S halfExtent N hN beta hbeta Q B n)

end

end MathlibAnalytic
end MGAP4D
