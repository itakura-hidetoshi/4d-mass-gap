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
Writing this constructor explicitly avoids asking typeclass synthesis for the
additive structure of the projected subtype `D.positiveTimeSubalgebra`. -/
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
      f x *
        f (periodicHypercubicEvenOpenHalfOrientationCorrection H y) := by
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

/-- **Quadratic polarization removes the apparent positive-half range
assumption.**

Suppose a concrete physical positive-time observable `F` has the desired
finite reflected readout `f`, and the explicitly constructed shifted observable
`F + 1` has the corresponding shifted readout `f + 1`. If the coherent
positive-half pullback is normalized on the unit, then its actual linear
readout of `F` is forced to be exactly `f`.

The proof uses no multiplicativity or surjectivity of `positiveHalfPullback`.
The quadratic identities for `F` and `F + 1`, together with linearity and the
unit, give for arbitrary independent open halves `x,y`

`(QF(x)-f(x)) + (QF(ρy)-f(ρy)) = 0`.

Fixing `y` makes the first difference constant; then substituting the same
orientation-corrected point in the first slot forces that constant to vanish.
This is the rank-one polarization step needed to turn concrete projective /
cylinder reflected identities into an exact positive-half preimage. -/
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
    nlinarith
  apply BoundedContinuousFunction.ext
  intro x
  let y0 : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N :=
    positiveHalfQuadraticPolarizationOpenHalfIdentity H N
  let z := periodicHypercubicEvenOpenHalfOrientationCorrection H y0
  have hx := hsum x y0
  have hz := hsum z y0
  change
    (Q.positiveHalfPullback n Fsub x - f x) +
      (Q.positiveHalfPullback n Fsub z - f z) = 0 at hx
  change
    (Q.positiveHalfPullback n Fsub z - f z) +
      (Q.positiveHalfPullback n Fsub z - f z) = 0 at hz
  have hz0 : Q.positiveHalfPullback n Fsub z - f z = 0 := by
    linarith
  have hx0 : Q.positiveHalfPullback n Fsub x - f x = 0 := by
    linarith
  exact sub_eq_zero.mp hx0

/-- A concrete pair of reflected cylinder identities therefore gives exact
membership in the coherent positive-half pullback range. This is the form
consumed by the existing finite-positive-half and `C⁰ → L²` bridges. -/
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

private theorem positiveHalfQuadraticPolarizationTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance positiveHalfQuadraticPolarizationSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- For the explicit SU(2) normalized-trace-power raw observable, Milestone 10
can now be discharged by constructing one physical positive-time cylinder
observable and proving its reflected readout for `F` and the explicit shifted
observable `F + 1`.

The conclusion is the concrete finite-positive-half range statement already
consumed by the exact trace-power `L²` and physical-excitation route. -/
theorem normalizedTracePowerRawActualAnalysisBounded_mem_finitePositiveHalfObservableRange_of_quadratic_polarization
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 positiveHalfQuadraticPolarizationTwoRankPositive beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n j : ℕ)
    (hUnit :
      Q.positiveHalfPullback n
          (positiveHalfQuadraticPolarizationUnit (S := S) (D := D)) =
        (1 : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) 2) ℝ))
    (F : D.positiveTimeSubalgebra)
    (hQuadratic : ∀ A,
      D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A)
    (hQuadraticAddOne : ∀ A,
      D.quadraticBoundedContinuousFunction
          (positiveHalfQuadraticPolarizationAddOne (D := D) F)
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
              (halfExtent n) (beta n) (hbeta n) j +
            (1 : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ)) A) :
    periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j ∈
      Set.range
        (fun G :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent 2 positiveHalfQuadraticPolarizationTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n).Carrier =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent 2 positiveHalfQuadraticPolarizationTwoRankPositive
              beta hbeta Q.toWeakStarBridge hInvariant n G) := by
  rw [Q.finitePositiveHalfObservable_range_eq_positiveHalfPullback_range
    hInvariant n]
  exact Q.mem_positiveHalfPullback_range_of_quadratic_polarization
    n hUnit F
      (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j)
      hQuadratic hQuadraticAddOne

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
