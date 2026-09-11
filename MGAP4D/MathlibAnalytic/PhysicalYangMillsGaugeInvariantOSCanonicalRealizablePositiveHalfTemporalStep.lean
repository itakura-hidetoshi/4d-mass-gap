import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalPositiveHalfSubalgebra
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizablePositiveTemporalCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

local instance canonicalRealizableTemporalStepSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalRealizableTemporalStepTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalRealizableTemporalStepCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalRealizableTemporalStepSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalRealizableTemporalStepMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalRealizableTemporalStepBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Restrict an actual integer temporal translate of the canonical positive-half
section back to the positive open half.  This is a literal finite-lattice map;
no abstract OS semigroup occurs in its definition. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
    (H N : ℕ) (k : ℤ)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N :=
  (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction
    (periodicHypercubicIntegerTemporalConfigurationTranslation
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
      (PeriodicHypercubicEvenSideLength H) k
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSection H N x))

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The canonical first-order half-support construction is also a value of the
newer coherent positive-time pullback interface.  No choice is introduced: the
interpolation and positive-half map are exactly the canonical ones. -/
noncomputable def toCanonicalCoherentPositiveTimePullback
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta) :
    PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S R₀.reflectionData halfExtent N hN beta hbeta where
  interpolate := R₀.interpolate
  interpolate_measurable := R₀.interpolate_measurable
  approximatingMeasure_toMeasure_eq := R₀.approximatingMeasure_toMeasure_eq
  positiveHalfPullback := R₀.toLinearHalfSupportReflection.positiveHalfPullback
  quadraticObservable_pullback := by
    intro n F A
    exact R₀.toLinearHalfSupportReflection.quadraticObservable_pullback n F A

@[simp] theorem toCanonicalCoherentPositiveTimePullback_interpolate
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    R₀.toCanonicalCoherentPositiveTimePullback.interpolate n = R₀.interpolate n :=
  rfl

@[simp] theorem toCanonicalCoherentPositiveTimePullback_positiveHalfPullback
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n =
      R₀.toLinearHalfSupportReflection.positiveHalfPullback n :=
  rfl

variable {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- For the canonical first-order finite-Wilson realization, every realizable
nonnegative physical time translation pulls back pointwise to the literal
integer temporal translation of the canonical positive-half section.

The proof uses only first-order observable support and interpolation covariance.
In particular it does not use an OS eigen-equation, a continuum limit, or a
Hamiltonian statement. -/
theorem canonicalPositiveHalfPullback_positiveTranslation_apply
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (n k : ℕ) (F : R₀.reflectionData.positiveTimeSubalgebra)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) :
    R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
        (⟨(R.positiveTranslation n k F).1, (R.positiveTranslation n k F).2⟩ :
          R₀.reflectionData.positiveTimeSubalgebra.toSubmodule) x =
      R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
        (⟨F.1, F.2⟩ : R₀.reflectionData.positiveTimeSubalgebra.toSubmodule)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
          (halfExtent n) N (Int.ofNat k) x) := by
  let L := R₀.toLinearHalfSupportReflection
  let A := periodicHypercubicEvenSpecialUnitaryPositiveHalfSection
    (halfExtent n) N x
  change L.positiveHalfPullback n
      (⟨(R.positiveTranslation n k F).1, (R.positiveTranslation n k F).2⟩ :
        R₀.reflectionData.positiveTimeSubalgebra.toSubmodule) x =
    L.positiveHalfPullback n
      (⟨F.1, F.2⟩ : R₀.reflectionData.positiveTimeSubalgebra.toSubmodule)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
        (halfExtent n) N (Int.ofNat k) x)
  calc
    L.positiveHalfPullback n
        (⟨(R.positiveTranslation n k F).1, (R.positiveTranslation n k F).2⟩ :
          R₀.reflectionData.positiveTimeSubalgebra.toSubmodule) x =
      (((R.positiveTranslation n k F : R₀.reflectionData.positiveTimeSubalgebra) :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ) (R₀.interpolate n A) := by
      symm
      simpa [L, A] using
        L.observable_pullback n (R.positiveTranslation n k F) A
    _ = (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
        (E.translate
          (R.toDiscreteTemporalCovariance.realizableTime n (Int.ofNat k))
          (R₀.interpolate n A))) := by
      simp only [R.positiveTranslation_coe,
        PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance.fullTranslation,
        PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizedGaugeInvariantObservableTranslation,
        physicalGaugeInvariantObservablePrecompAlgEquiv_apply]
    _ = (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ)
        (R₀.interpolate n
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength (halfExtent n)) (Int.ofNat k) A))) := by
      have hEq :=
        R.toDiscreteTemporalCovariance.interpolate_integerTemporal_equivariant
          n (Int.ofNat k) A
      have hEval := congrArg
        (fun X => (((F : physicalYangMillsGaugeInvariantObservableSubalgebra S) :
          BoundedContinuousFunction S.Configuration ℝ) X)) hEq
      simpa [PhysicalYangMillsEvenPeriodicWilsonOSCoherentDiscreteTemporalCovariance.realizableTime,
        toCanonicalCoherentPositiveTimePullback] using hEval.symm
    _ = L.positiveHalfPullback n
        (⟨F.1, F.2⟩ : R₀.reflectionData.positiveTimeSubalgebra.toSubmodule)
        ((periodicHypercubicEvenEdgeOrbitPartition (halfExtent n)).positiveRestriction
          (periodicHypercubicIntegerTemporalConfigurationTranslation
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
            (PeriodicHypercubicEvenSideLength (halfExtent n)) (Int.ofNat k) A)) := by
      exact L.observable_pullback n F _
    _ = L.positiveHalfPullback n
        (⟨F.1, F.2⟩ : R₀.reflectionData.positiveTimeSubalgebra.toSubmodule)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
          (halfExtent n) N (Int.ofNat k) x) := by
      rfl

/-- One-lattice-step specialization of the canonical finite pullback formula. -/
theorem canonicalPositiveHalfPullback_positiveTranslation_one_apply
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (n : ℕ) (F : R₀.reflectionData.positiveTimeSubalgebra)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) :
    R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
        (⟨(R.positiveTranslation n 1 F).1, (R.positiveTranslation n 1 F).2⟩ :
          R₀.reflectionData.positiveTimeSubalgebra.toSubmodule) x =
      R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
        (⟨F.1, F.2⟩ : R₀.reflectionData.positiveTimeSubalgebra.toSubmodule)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
          (halfExtent n) N 1 x) := by
  simpa using R₀.canonicalPositiveHalfPullback_positiveTranslation_apply R n 1 F x

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end
end MathlibAnalytic
end MGAP4D
