import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryMomentGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryPositiveHalfPathAmplitude
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance osBoundaryMomentPathBridgeEvenSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance osBoundaryMomentPathBridgeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryMomentPathBridgeSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryMomentPathBridgeSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryMomentPathBridgeSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryMomentPathBridgeSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The concrete shared-boundary moment is exactly the finite-volume
`Z^{-1/2}` normalization of the positive-half Wilson path amplitude with the
open-half observable inserted.

This theorem exposes the path-integral object hidden behind
`periodicHypercubicEvenBoundaryObservableMoment`; it adds no decay or
uniformity assumption. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_eq_invSqrtPartition_mul_osAmplitudeMoment
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryObservableMoment
        H N hN beta hbeta f b =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹ *
        ∫ x,
          periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
            H N hN beta hbeta b x * f x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  simpa only [periodicHypercubicEvenBoundaryObservableMoment] using
    (periodicHypercubicEvenBoundaryObservableGramMoment_eq_invSqrtPartition_mul_osAmplitudeMoment
      H N hN beta hbeta f b)

/-- For the actual `n`-th approximating Wilson OS carrier, the abstractly named
shared-boundary moment is the same concrete inserted positive-half path
amplitude, with its finite-volume partition normalization displayed exactly.

This is the adapter needed to feed transfer/path estimates into the existing
boundary-moment gap certificates without identifying a general bulk insertion
with a bare transfer power. -/
theorem physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_eq_invSqrtPartition_mul_osAmplitudeMoment
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
        S D halfExtent N hN beta hbeta B hInvariant n F b =
      (Real.sqrt
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n)) N hN
            (beta n) (hbeta n)).base.partitionFunction)⁻¹ *
        ∫ x,
          periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
              (halfExtent n) N hN (beta n) (hbeta n) b x *
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent N hN beta hbeta B hInvariant n F x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
  exact
    periodicHypercubicEvenBoundaryObservableMoment_eq_invSqrtPartition_mul_osAmplitudeMoment
      (halfExtent n) N hN (beta n) (hbeta n)
      (fun x =>
        physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
          S D halfExtent N hN beta hbeta B hInvariant n F x)
      b

end MathlibAnalytic
end MGAP4D
