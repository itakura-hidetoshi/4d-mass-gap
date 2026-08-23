import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCommonPositiveHalfPullback
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSConfigurationTimeTranslation

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance actualLinearHalfSupportSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualLinearHalfSupportSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualLinearHalfSupportSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualLinearHalfSupportSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualLinearHalfSupportSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualLinearHalfSupportSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Model-facing realization of actual finite-Wilson positive-time support.

Compared with `PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback`,
this structure no longer assumes a quadratic `Theta(F) * F` pullback identity.
Instead it records only first-order data:

* one observable-independent lattice interpolation at every scale;
* one real-linear positive-open-half pullback;
* pointwise factorization of every positive-time observable through the
  positive restriction of the lattice configuration;
* realization of physical OS reflection by one configuration reflection;
* covariance of interpolation with the actual even-periodic lattice
  configuration reflection.

The quadratic reflected-observable identity is theorem-generated below by
multiplicativity and commutativity of the real observable algebra. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
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
  configurationReflection : Homeomorph S.Configuration S.Configuration
  reflection_gauge_commute : ∀ g X,
    configurationReflection (S.action g X) =
      S.action g (configurationReflection X)
  reflection_realization : ∀ O,
    D.reflection O =
      physicalGaugeInvariantObservablePrecompAlgEquiv S
        configurationReflection reflection_gauge_commute O
  interpolate_reflection :
    ∀ n A,
      configurationReflection (interpolate n A) =
        interpolate n
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)
  observable_pullback :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra)
      (A : PeriodicHypercubicEvenEdge (halfExtent n) →
        Matrix.specialUnitaryGroup (Fin N) ℂ),
      (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) (interpolate n A)) =
        positiveHalfPullback n ⟨F.1, F.2⟩
          ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction A)

namespace PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Configuration-level reflection covariance plus first-order half support
identifies the pullback of the reflected physical observable. -/
theorem reflectedObservable_pullback
    (R : PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
      S D halfExtent N hN beta hbeta)
    (n : ℕ) (F : D.positiveTimeSubalgebra)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (((D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ) (R.interpolate n A)) =
      R.positiveHalfPullback n ⟨F.1, F.2⟩
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
          (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)) := by
  rw [R.reflection_realization]
  change
    (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
      (R.configurationReflection (R.interpolate n A))) = _
  rw [R.interpolate_reflection n A]
  exact R.observable_pullback n F
    (periodicHypercubicEvenConfigurationReflection (halfExtent n) A)

/-- The quadratic OS pullback required by the actual finite Wilson reflection
positivity bridge is generated from the two first-order pullbacks. -/
theorem quadraticObservable_pullback
    (R : PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
      S D halfExtent N hN beta hbeta)
    (n : ℕ) (F : D.positiveTimeSubalgebra)
    (A : PeriodicHypercubicEvenEdge (halfExtent n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    D.quadraticBoundedContinuousFunction F (R.interpolate n A) =
      periodicHypercubicEvenFullReflectedObservable
        (halfExtent n) (R.positiveHalfPullback n ⟨F.1, F.2⟩) A := by
  change
    (((D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
      BoundedContinuousFunction S.Configuration ℝ) (R.interpolate n A)) *
      (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (R.interpolate n A)) = _
  rw [R.reflectedObservable_pullback n F A]
  rw [R.observable_pullback n F A]
  unfold periodicHypercubicEvenFullReflectedObservable
  rw [mul_comm]

/-- First-order positive-half support and reflection covariance generate the
common actual Wilson positive-half pullback interface of PR #2048. -/
noncomputable def toCommonPositiveHalfPullback
    (R : PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
      S D halfExtent N hN beta hbeta) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonPositiveHalfPullback
      S D halfExtent N hN beta hbeta where
  interpolate := R.interpolate
  interpolate_measurable := R.interpolate_measurable
  positiveHalfPullback := R.positiveHalfPullback
  approximatingMeasure_toMeasure_eq := R.approximatingMeasure_toMeasure_eq
  quadraticObservable_pullback := fun n F A =>
    R.quadraticObservable_pullback n F A

@[simp] theorem toCommonPositiveHalfPullback_positiveHalfPullback
    (R : PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
      S D halfExtent N hN beta hbeta)
    (n : ℕ) :
    R.toCommonPositiveHalfPullback.positiveHalfPullback n =
      R.positiveHalfPullback n :=
  rfl

/-- Hence the first-order model data already generate the actual separated OS
isometry into the shared-boundary Haar `L²` representation. -/
noncomputable def toSeparatedBoundaryMomentLinearIsometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta
        R.toCommonPositiveHalfPullback.toWeakStarBridge hInvariant n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  R.toCommonPositiveHalfPullback.toSeparatedBoundaryMomentLinearIsometry
    hInvariant n

@[simp] theorem toSeparatedBoundaryMomentLinearIsometry_mk
    (R : PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta
        R.toCommonPositiveHalfPullback.toWeakStarBridge hInvariant n).Carrier) :
    R.toSeparatedBoundaryMomentLinearIsometry hInvariant n
        (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta
          R.toCommonPositiveHalfPullback.toWeakStarBridge hInvariant n F := by
  exact R.toCommonPositiveHalfPullback.toSeparatedBoundaryMomentLinearIsometry_mk
    hInvariant n F

end PhysicalYangMillsEvenPeriodicWilsonOSLinearHalfSupportReflection

end

end MathlibAnalytic
end MGAP4D
