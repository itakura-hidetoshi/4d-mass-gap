import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizablePositiveHalfTemporalStep
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableDiscreteSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentAdjointSynthesis
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

local instance canonicalRealizableTemporalL2StepSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalRealizableTemporalL2StepTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalRealizableTemporalL2StepCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalRealizableTemporalL2StepSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalRealizableTemporalL2StepMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalRealizableTemporalL2StepBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}

/-- The canonical finite positive-half observable of an actually translated OS
carrier is pointwise the original canonical pullback evaluated on the literal
integer temporal translate of the positive-half section.

This is the carrier-level form of the exact lattice-time formula.  No common
`NNReal` semigroup, completion, eigen-equation, or Hamiltonian input occurs. -/
theorem canonicalFinitePositiveHalfObservable_realizableCarrierTranslation_apply
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (hInvariant : ∀ n,
      R₀.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).Carrier)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
      (halfExtent n) N) :
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n
        (R.realizableCarrierTranslation hInvariant n k F) x =
      R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S R₀.reflectionData halfExtent N hN beta hbeta
            R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).toPositiveTime F)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
          (halfExtent n) N (Int.ofNat k) x) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n
  change
    R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
        (Pn.toPositiveTime (R.realizableCarrierTranslation hInvariant n k F)) x = _
  simpa [Pn] using
    R₀.canonicalPositiveHalfPullback_positiveTranslation_apply
      R n k (Pn.positiveTimeElement F) x

/-- The preceding literal lattice-time identity survives canonically in the
actual open-half Haar `L²` carrier: a representative of the translated feature
vector is almost everywhere the original positive-half pullback evaluated on
the one integer-step section map.

The only analytic input is Mathlib's canonical `BoundedContinuousFunction.toLp`
representative theorem. -/
theorem canonicalPositiveHalfL2_realizableCarrierTranslation_coeFn
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (hInvariant : ∀ n,
      R₀.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).Carrier) :
    (fun x =>
      R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfL2LinearMap
        hInvariant n (R.realizableCarrierTranslation hInvariant n k F) x) =ᵐ[
      periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N]
      (fun x =>
        R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S R₀.reflectionData halfExtent N hN beta hbeta
              R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).toPositiveTime F)
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
            (halfExtent n) N (Int.ofNat k) x)) := by
  let G := R.realizableCarrierTranslation hInvariant n k F
  have hcoe :=
    periodicHypercubicEvenWilsonOpenHalfObservableL2_coeFn
      (halfExtent n) N
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S R₀.reflectionData halfExtent N hN beta hbeta
          R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n G)
  filter_upwards [hcoe] with x hx
  change
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S R₀.reflectionData halfExtent N hN beta hbeta
          R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n G x = _
  rw [show
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
        S R₀.reflectionData halfExtent N hN beta hbeta
          R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n G x =
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S R₀.reflectionData halfExtent N hN beta hbeta
          R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n G x by
    exact hx]
  exact R₀.canonicalFinitePositiveHalfObservable_realizableCarrierTranslation_apply
    R hInvariant n k F x

/-- One-lattice-step specialization of the actual open-half `L²` representative. -/
theorem canonicalPositiveHalfL2_realizableCarrierTranslation_one_coeFn
    (R₀ : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback E)
    (hInvariant : ∀ n,
      R₀.reflectionData.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R₀.reflectionData halfExtent N hN beta hbeta
        R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).Carrier) :
    (fun x =>
      R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfL2LinearMap
        hInvariant n (R.realizableCarrierTranslation hInvariant n 1 F) x) =ᵐ[
      periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N]
      (fun x =>
        R₀.toCanonicalCoherentPositiveTimePullback.positiveHalfPullback n
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S R₀.reflectionData halfExtent N hN beta hbeta
              R₀.toCanonicalCoherentPositiveTimePullback.toWeakStarBridge hInvariant n).toPositiveTime F)
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfSectionIntegerTemporalStep
            (halfExtent n) N 1 x)) := by
  simpa using R₀.canonicalPositiveHalfL2_realizableCarrierTranslation_coeFn
    R hInvariant n 1 F

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end
end MathlibAnalytic
end MGAP4D
