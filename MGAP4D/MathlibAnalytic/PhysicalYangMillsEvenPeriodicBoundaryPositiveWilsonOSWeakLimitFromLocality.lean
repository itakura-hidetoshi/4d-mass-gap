import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveObservableDescent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocalitySideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocalitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocalitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocalitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocalitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitFromLocalitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Construct the boundary-positive actual-Wilson weak-limit bridge directly
from locality of a full finite observable.

The only finite-observable hypothesis is negative-half independence: at fixed
reflection boundary and positive open half, the observable does not depend on
the negative open half.  The canonical descent from #1776 then supplies the
boundary-positive observable, and its reflected product is definitionally
identified with the ordinary full reflected product.

No finite reflection-positivity premise is stored here. -/
noncomputable def
    physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge_of_negativeHalfIndependent
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : BoundedContinuousFunction S.Configuration ℝ)
    (interpolate : ∀ n,
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map (interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure)
    (f : ∀ n, BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (hind : ∀ n,
      (periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).NegativeHalfIndependent
        (fun A => f n A))
    (quadraticObservable_pullback : ∀ n A,
      Q (interpolate n A) =
        f n A *
          f n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) :
    PhysicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge
      S halfExtent N hN beta hbeta Q where
  interpolate := interpolate
  interpolate_measurable := interpolate_measurable
  boundaryPositiveObservable := fun n =>
    periodicHypercubicEvenBoundaryPositiveObservableOfFull
      (halfExtent n) (f n)
  approximatingMeasure_toMeasure_eq := approximatingMeasure_toMeasure_eq
  quadraticObservable_pullback := by
    intro n A
    calc
      Q (interpolate n A) =
          f n A *
            f n (periodicHypercubicEvenConfigurationReflection
              (halfExtent n) A) :=
        quadraticObservable_pullback n A
      _ = periodicHypercubicEvenBoundaryPositiveFullReflectedObservable
          (halfExtent n)
          (periodicHypercubicEvenBoundaryPositiveObservableOfFull
            (halfExtent n) (f n)) A := by
        symm
        exact
          periodicHypercubicEvenBoundaryPositiveFullReflectedObservable_descent_eq
            (halfExtent n) (f n) (hind n) A

/-- The locality constructor immediately yields nonnegativity of every physical
approximating expectation.  The actual Wilson reflection-positivity theorem is
used downstream by the pre-existing boundary-positive weak-limit theorem, not
assumed here. -/
theorem
    physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_nonneg_of_negativeHalfIndependent
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : BoundedContinuousFunction S.Configuration ℝ)
    (interpolate : ∀ n,
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map (interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure)
    (f : ∀ n, BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (hind : ∀ n,
      (periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).NegativeHalfIndependent
        (fun A => f n A))
    (quadraticObservable_pullback : ∀ n A,
      Q (interpolate n A) =
        f n A *
          f n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A))
    (n : ℕ) :
    0 ≤ ∫ A, Q A ∂(S.approximatingMeasure n : Measure S.Configuration) := by
  let B :=
    physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge_of_negativeHalfIndependent
      S halfExtent N hN beta hbeta Q interpolate interpolate_measurable
      approximatingMeasure_toMeasure_eq f hind quadraticObservable_pullback
  exact
    physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_approximating_nonneg
      S halfExtent N hN beta hbeta Q B n

/-- Negative-half locality plus exact physical pullback therefore passes all the
way to the continuum weak limit.  This is the generic locality-to-continuum OS
nonnegativity route used by concrete cylinder observables. -/
theorem
    physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_continuum_nonneg_of_negativeHalfIndependent
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : BoundedContinuousFunction S.Configuration ℝ)
    (interpolate : ∀ n,
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        S.Configuration)
    (interpolate_measurable : ∀ n, Measurable (interpolate n))
    (approximatingMeasure_toMeasure_eq : ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map (interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure)
    (f : ∀ n, BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (hind : ∀ n,
      (periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).NegativeHalfIndependent
        (fun A => f n A))
    (quadraticObservable_pullback : ∀ n A,
      Q (interpolate n A) =
        f n A *
          f n (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) :
    0 ≤ ∫ A, Q A ∂(S.continuumMeasure : Measure S.Configuration) := by
  let B :=
    physicalYangMillsEvenPeriodicBoundaryPositiveWilsonOSWeakLimitBridge_of_negativeHalfIndependent
      S halfExtent N hN beta hbeta Q interpolate interpolate_measurable
      approximatingMeasure_toMeasure_eq f hind quadraticObservable_pullback
  exact
    physical_yang_mills_evenPeriodicBoundaryPositiveWilsonOS_continuum_nonneg
      S halfExtent N hN beta hbeta Q B

end

end MathlibAnalytic
end MGAP4D
