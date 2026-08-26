import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalCompletedBoundarySpatialSlicePairL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHilbertSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance periodicHypercubicEvenOSBoundaryPairL2SpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- On the dense family represented by positive-time observables, the completed
finite-volume OS time-translation operator is transported by the canonical
closed-image realization to the exact two-spatial-slice boundary moment of the
translated observable.

This is the operator-side step that was deliberately absent from the earlier
carrier-identification theorem.  It introduces no one-slab-transfer claim: the
next required input is the Wilson kernel factorization identifying the
translated two-slice moment with the actual one-slab kernel pairing. -/
theorem toCompletedSpatialSlicePairMomentLinearIsometryAutomatic_finiteOperator_on_positiveTimeObservable
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ)
    (t : NNReal)
    (F : R.reflectionData.positiveTimeSubalgebra) :
    let P :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S R.reflectionData halfExtent N hN beta hbeta
          R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
          R.approximatingReflectionInvariantFamily n
    R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n
        (C.finiteOperator n t
          (P.physicalState (P.carrierOfPositiveTime F))) =
      periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2
        (halfExtent n) N
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n
            (P.carrierOfPositiveTime (C.translate t F))) := by
  dsimp only
  rw [C.finiteOperator_on_positiveTimeObservable]
  exact
    R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic_physicalState
      n _

/-- Pointwise-a.e. form of the dense operator transport.  After applying the
completed OS-to-pair isometry, finite OS time translation is represented by the
translated canonical boundary moment literally composed with the inverse
boundary/two-slice coordinate equivalence.

This exposes the exact pair variables on which the actual one-slab Wilson
kernel lives, without postulating any equality with that kernel. -/
theorem toCompletedSpatialSlicePairMomentLinearIsometryAutomatic_finiteOperator_on_positiveTimeObservable_coeFn
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ)
    (t : NNReal)
    (F : R.reflectionData.positiveTimeSubalgebra) :
    let P :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S R.reflectionData halfExtent N hN beta hbeta
          R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
          R.approximatingReflectionInvariantFamily n
    R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n
        (C.finiteOperator n t
          (P.physicalState (P.carrierOfPositiveTime F))) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
        (halfExtent n) N]
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S R.reflectionData halfExtent N hN beta hbeta
          R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
          R.approximatingReflectionInvariantFamily n
          (P.carrierOfPositiveTime (C.translate t F))) ∘
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv
          (halfExtent n) (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm := by
  dsimp only
  rw [R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic_finiteOperator_on_positiveTimeObservable
    C n t F]
  exact
    periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2_coeFn
      (halfExtent n) N _

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
