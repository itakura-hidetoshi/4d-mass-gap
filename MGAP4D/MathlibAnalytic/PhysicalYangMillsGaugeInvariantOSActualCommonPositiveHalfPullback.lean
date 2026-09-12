import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualPositiveHalfLinearBoundaryRepresentation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance actualCommonPositiveHalfSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualCommonPositiveHalfSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualCommonPositiveHalfSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualCommonPositiveHalfSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualCommonPositiveHalfSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualCommonPositiveHalfSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A common finite-Wilson pullback realization for the whole physical
positive-time observable algebra.

The older weak-star bridge chooses a full finite bridge separately for each
positive-time observable.  Here the lattice interpolation and the pullback to
the positive open half are shared across all observables.  The latter is
bundled on the underlying positive-time real submodule, matching the carrier
used by the OS bilinear form and avoiding nested-subalgebra instance search.

The only remaining model-specific identity is the actual support/factorization
statement saying that the pulled-back physical OS quadratic observable is the
finite reflected observable built from this common positive-half pullback. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n) where
  interpolate :
    ∀ n,
      (PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        S.Configuration
  interpolate_measurable : ∀ n, Measurable (interpolate n)
  positiveHalfPullback :
    ∀ n,
      D.positiveTimeSubalgebra.toSubmodule →ₗ[ℝ]
        BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) N) ℝ
  approximatingMeasure_toMeasure_eq :
    ∀ n,
      (S.approximatingMeasure n : Measure S.Configuration) =
        Measure.map (interpolate n)
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure
  quadraticObservable_pullback :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (A : PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ),
      D.quadraticBoundedContinuousFunction F (interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable
          (halfExtent n)
          (positiveHalfPullback n ⟨F.1, F.2⟩) A

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- A common linear positive-half pullback generates the older per-observable
finite Wilson weak-star bridge.  Every generated finite bridge uses the same
interpolation map; only the linearly pulled-back positive-half observable
depends on `F`. -/
noncomputable def toWeakStarBridge
    (C : PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
      S D halfExtent N hN beta hbeta) :
    PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta where
  finiteBridge := fun F =>
    { interpolate := C.interpolate
      interpolate_measurable := C.interpolate_measurable
      positiveHalfObservable := fun n =>
        C.positiveHalfPullback n ⟨F.1, F.2⟩
      approximatingMeasure_toMeasure_eq := C.approximatingMeasure_toMeasure_eq
      quadraticObservable_pullback := fun n A =>
        C.quadraticObservable_pullback n F A }

@[simp] theorem toWeakStarBridge_positiveHalfObservable
    (C : PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
      S D halfExtent N hN beta hbeta)
    (F : D.positiveTimeSubalgebra)
    (n : ℕ) :
    ((C.toWeakStarBridge.finiteBridge F).positiveHalfObservable n) =
      C.positiveHalfPullback n ⟨F.1, F.2⟩ :=
  rfl

/-- For the bridge generated by a common pullback, the finite positive-half
observable attached to an OS carrier is literally the common linear pullback
of its positive-time submodule representative. -/
theorem finitePositiveHalfObservable_eq_positiveHalfPullback
    (C : PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n F =
      C.positiveHalfPullback n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n).toPositiveTime F) :=
  rfl

/-- The common linear pullback theorem-generates the positive-half observable
coherence used by the actual Wilson boundary representation. -/
noncomputable def toFinitePositiveHalfObservableLinearCoherence
    (C : PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableLinearCoherence
      S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant where
  map_add := by
    intro n F G
    rw [C.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n (F + G)]
    rw [C.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n F]
    rw [C.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n G]
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n
    change
      C.positiveHalfPullback n (Pn.toPositiveTime (F + G)) =
        C.positiveHalfPullback n (Pn.toPositiveTime F) +
          C.positiveHalfPullback n (Pn.toPositiveTime G)
    rw [Pn.toPositiveTime_add]
    exact (C.positiveHalfPullback n).map_add _ _
  map_smul := by
    intro n r F
    rw [C.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n (r • F)]
    rw [C.finitePositiveHalfObservable_eq_positiveHalfPullback hInvariant n F]
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n
    change
      C.positiveHalfPullback n (Pn.toPositiveTime (r • F)) =
        r • C.positiveHalfPullback n (Pn.toPositiveTime F)
    rw [Pn.toPositiveTime_smul]
    exact (C.positiveHalfPullback n).map_smul r _

/-- Consequently one common positive-half pullback realization generates the
full separated actual Wilson boundary representation. -/
noncomputable def toSeparatedBoundaryMomentLinearIsometry
    (C : PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  (C.toFinitePositiveHalfObservableLinearCoherence hInvariant)
    |>.toSeparatedBoundaryMomentLinearIsometry n

@[simp] theorem toSeparatedBoundaryMomentLinearIsometry_mk
    (C : PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n).Carrier) :
    C.toSeparatedBoundaryMomentLinearIsometry hInvariant n (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta C.toWeakStarBridge hInvariant n F := by
  exact
    (C.toFinitePositiveHalfObservableLinearCoherence hInvariant)
      |>.toSeparatedBoundaryMomentLinearIsometry_mk n F

end PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback

end

end MathlibAnalytic
end MGAP4D
