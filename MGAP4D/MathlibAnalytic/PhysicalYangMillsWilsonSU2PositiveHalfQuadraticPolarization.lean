import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerFinitePositiveHalfObservableBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

local instance positiveHalfQuadraticPolarizationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfQuadraticPolarizationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfQuadraticPolarizationSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfQuadraticPolarizationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfQuadraticPolarizationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

private def positiveHalfQuadraticPolarizationUnit
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S} :
    D.positiveTimeSubalgebra.toSubmodule :=
  ⟨(1 : physicalYangMillsGaugeInvariantObservableSubalgebra S),
    D.positiveTimeSubalgebra.one_mem⟩

/-- The shifted positive-time observable, constructed in the ambient observable
algebra and returned to the positive-time subalgebra by `Subalgebra.add_mem`.
This avoids projected-subtype typeclass search. -/
private def positiveHalfQuadraticPolarizationAddOne
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (F : D.positiveTimeSubalgebra) : D.positiveTimeSubalgebra :=
  ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S) +
      (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S),
    D.positiveTimeSubalgebra.add_mem F.2 D.positiveTimeSubalgebra.one_mem⟩

private def positiveHalfQuadraticPolarizationBoundaryIdentity
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N :=
  fun _ => 1

private def positiveHalfQuadraticPolarizationOpenHalfIdentity
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N :=
  fun _ => 1

/-- The scalar polarization identity used by the positive-half reconstruction.
Keeping the nonlinear arithmetic independent of the gauge-theory types makes
the main theorem both transparent and inexpensive to elaborate. -/
private theorem positiveHalfQuadraticPolarization_cross_sum
    (a b c d : ℝ)
    (h0 : a * b = c * d)
    (h1 : (a + 1) * (b + 1) = (c + 1) * (d + 1)) :
    (a - c) + (b - d) = 0 := by
  nlinarith

/-- If the difference of two real-valued functions is paired with the same
reflected difference to zero for every pair of points, then the functions are
pointwise equal. -/
private theorem positiveHalfQuadraticPolarization_pointwise_eq
    {X : Type*}
    (g f : X → ℝ)
    (rho : X → X)
    (y0 : X)
    (hsum : ∀ x y, (g x - f x) + (g (rho y) - f (rho y)) = 0) :
    ∀ x, g x = f x := by
  intro x
  have hx := hsum x y0
  have hz := hsum (rho y0) y0
  linarith

/-- Boundary-fibered assembly evaluates a reflected positive-half observable as
an honest rank-one product in the two independently variable open halves. -/
theorem periodicHypercubicEvenFullReflectedObservable_boundaryFiberedAssemble
    (H N : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenFullReflectedObservable H f
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  unfold periodicHypercubicEvenFullReflectedObservable
  rw [periodicHypercubicEvenPositiveRestriction_configurationReflection]
  change
    f (P.positiveRestriction (P.boundaryFiberedAssemble b x y)) *
        f (periodicHypercubicEvenOpenHalfOrientationCorrection H
          (P.negativeRestriction (P.boundaryFiberedAssemble b x y))) = _
  rw [P.positiveRestriction_boundaryFiberedAssemble,
    P.negativeRestriction_boundaryFiberedAssemble]

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- **Quadratic polarization reconstructs the exact positive-half readout.**

Suppose a concrete physical positive-time observable `F` has finite reflected
readout `f`, while the explicitly constructed shifted observable `F + 1` has
readout `f + 1`. If the coherent positive-half pullback is normalized on the
unit, linearity and the two quadratic identities force its readout of `F` to
be exactly `f`.

No multiplicativity or surjectivity of `positiveHalfPullback` is used. -/
theorem positiveHalfPullback_eq_of_quadratic_polarization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ)
    (hUnit :
      Q.positiveHalfPullback n
          (positiveHalfQuadraticPolarizationUnit (S := S) (D := D)) =
        (1 : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) N) ℝ))
    (F : D.positiveTimeSubalgebra)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) N) ℝ)
    (hQuadratic : ∀ A,
      D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n) f A)
    (hQuadraticAddOne : ∀ A,
      D.quadraticBoundedContinuousFunction
          (positiveHalfQuadraticPolarizationAddOne (D := D) F)
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (f + (1 : BoundedContinuousFunction
            (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
              (halfExtent n) N) ℝ)) A) :
    Q.positiveHalfPullback n
        (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule) = f := by
  let H := halfExtent n
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let b0 : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N :=
    positiveHalfQuadraticPolarizationBoundaryIdentity H N
  let Fsub : D.positiveTimeSubalgebra.toSubmodule := ⟨F.1, F.2⟩
  let unit : D.positiveTimeSubalgebra.toSubmodule :=
    positiveHalfQuadraticPolarizationUnit (S := S) (D := D)
  let Fadd : D.positiveTimeSubalgebra :=
    positiveHalfQuadraticPolarizationAddOne (D := D) F
  have hFadd :
      (⟨Fadd.1, Fadd.2⟩ : D.positiveTimeSubalgebra.toSubmodule) =
        Fsub + unit := by
    rfl
  have hPullAdd :
      Q.positiveHalfPullback n
          (⟨Fadd.1, Fadd.2⟩ : D.positiveTimeSubalgebra.toSubmodule) =
        Q.positiveHalfPullback n Fsub +
          (1 : BoundedContinuousFunction
            (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
              (halfExtent n) N) ℝ) := by
    rw [hFadd, (Q.positiveHalfPullback n).map_add]
    change Q.positiveHalfPullback n Fsub +
        Q.positiveHalfPullback n
          (positiveHalfQuadraticPolarizationUnit (S := S) (D := D)) = _
    rw [hUnit]
  have hsum : ∀ x y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
      (Q.positiveHalfPullback n Fsub x - f x) +
        (Q.positiveHalfPullback n Fsub
            (periodicHypercubicEvenOpenHalfOrientationCorrection H y) -
          f (periodicHypercubicEvenOpenHalfOrientationCorrection H y)) = 0 := by
    intro x y
    let A : PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ :=
      P.boundaryFiberedAssemble b0 x y
    have h0raw :=
      (Q.quadraticObservable_pullback n F A).symm.trans (hQuadratic A)
    have h1raw :=
      (Q.quadraticObservable_pullback n Fadd A).symm.trans
        (hQuadraticAddOne A)
    have h0 :
        Q.positiveHalfPullback n Fsub x *
            Q.positiveHalfPullback n Fsub
              (periodicHypercubicEvenOpenHalfOrientationCorrection H y) =
          f x * f (periodicHypercubicEvenOpenHalfOrientationCorrection H y) := by
      dsimp only [A] at h0raw
      rw [periodicHypercubicEvenFullReflectedObservable_boundaryFiberedAssemble,
        periodicHypercubicEvenFullReflectedObservable_boundaryFiberedAssemble] at h0raw
      simpa only [Fsub] using h0raw
    have h1 :
        (Q.positiveHalfPullback n Fsub x + 1) *
            (Q.positiveHalfPullback n Fsub
              (periodicHypercubicEvenOpenHalfOrientationCorrection H y) + 1) =
          (f x + 1) *
            (f (periodicHypercubicEvenOpenHalfOrientationCorrection H y) + 1) := by
      rw [hPullAdd] at h1raw
      dsimp only [A] at h1raw
      rw [periodicHypercubicEvenFullReflectedObservable_boundaryFiberedAssemble,
        periodicHypercubicEvenFullReflectedObservable_boundaryFiberedAssemble] at h1raw
      simpa only [Fsub, BoundedContinuousFunction.add_apply] using h1raw
    exact positiveHalfQuadraticPolarization_cross_sum
      (Q.positiveHalfPullback n Fsub x)
      (Q.positiveHalfPullback n Fsub
        (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      (f x)
      (f (periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      h0 h1
  apply BoundedContinuousFunction.ext
  intro x
  exact positiveHalfQuadraticPolarization_pointwise_eq
    (fun z => Q.positiveHalfPullback n Fsub z)
    (fun z => f z)
    (periodicHypercubicEvenOpenHalfOrientationCorrection H)
    (positiveHalfQuadraticPolarizationOpenHalfIdentity H N)
    hsum x

/-- A concrete pair of reflected cylinder identities therefore gives exact
membership in the coherent positive-half pullback range. -/
theorem mem_positiveHalfPullback_range_of_quadratic_polarization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (n : ℕ)
    (hUnit :
      Q.positiveHalfPullback n
          (positiveHalfQuadraticPolarizationUnit (S := S) (D := D)) =
        (1 : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) N) ℝ))
    (F : D.positiveTimeSubalgebra)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) N) ℝ)
    (hQuadratic : ∀ A,
      D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n) f A)
    (hQuadraticAddOne : ∀ A,
      D.quadraticBoundedContinuousFunction
          (positiveHalfQuadraticPolarizationAddOne (D := D) F)
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (f + (1 : BoundedContinuousFunction
            (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
              (halfExtent n) N) ℝ)) A) :
    f ∈ LinearMap.range (Q.positiveHalfPullback n) := by
  refine ⟨(⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule), ?_⟩
  exact Q.positiveHalfPullback_eq_of_quadratic_polarization
    n hUnit F f hQuadratic hQuadraticAddOne

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
