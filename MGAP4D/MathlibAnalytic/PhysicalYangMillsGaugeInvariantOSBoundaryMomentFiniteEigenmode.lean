import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundarySpatialSlicePairL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Equality after the canonical completed OS-to-two-slice pair realization
reflects back to equality in the actual finite Wilson OS Hilbert space.

This is the type-correct replacement for a global identification of the finite
OS Hilbert carrier with the full pair-`L²` carrier: only injectivity of the
already-constructed canonical linear isometry is used. -/
theorem finiteOperator_apply_eq_smul_of_completedSpatialSlicePairMoment
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ) (t : NNReal)
    (phi : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert)
    (mu : ℝ)
    (hPair : R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n
        (C.finiteOperator n t phi) =
      mu • R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n phi) :
    C.finiteOperator n t phi = mu • phi := by
  apply (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n).injective
  simpa using hPair

/-- A pair-`L²` eigen-equation for the canonical boundary moments of a positive-
time observable and its translate is already an eigen-equation for the actual
completed finite Wilson OS transfer operator. -/
theorem finiteOperator_on_positiveTimeObservable_of_pairMoment_eigen
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ) (t : NNReal) (F : R.reflectionData.positiveTimeSubalgebra) (mu : ℝ)
    (hPair :
      periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2
          (halfExtent n) N
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S R.reflectionData halfExtent N hN beta hbeta
              R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
              R.approximatingReflectionInvariantFamily n
              ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S R.reflectionData halfExtent N hN beta hbeta
                  R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
                  R.approximatingReflectionInvariantFamily n).carrierOfPositiveTime
                    (C.translate t F))) =
        mu • periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2
          (halfExtent n) N
          (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S R.reflectionData halfExtent N hN beta hbeta
              R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
              R.approximatingReflectionInvariantFamily n
              ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S R.reflectionData halfExtent N hN beta hbeta
                  R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
                  R.approximatingReflectionInvariantFamily n).carrierOfPositiveTime F))) :
    let P := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n
    C.finiteOperator n t (P.physicalState (P.carrierOfPositiveTime F)) =
      mu • P.physicalState (P.carrierOfPositiveTime F) := by
  dsimp only
  apply R.finiteOperator_apply_eq_smul_of_completedSpatialSlicePairMoment C
  rw [R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic_finiteOperator_on_positiveTimeObservable
    C n t F]
  rw [R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic_physicalState]
  exact hPair

/-- It is enough to verify the eigen-equation before the final boundary-to-pair
coordinate isometry.  Linearity then transports it to the actual one-slab
pair-`L²` carrier, where the preceding theorem reflects it back into the finite
Wilson OS Hilbert space. -/
theorem finiteOperator_on_positiveTimeObservable_of_boundaryMoment_eigen
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ) (t : NNReal) (F : R.reflectionData.positiveTimeSubalgebra) (mu : ℝ)
    (hMoment :
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S R.reflectionData halfExtent N hN beta hbeta
                R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
                R.approximatingReflectionInvariantFamily n).carrierOfPositiveTime
                  (C.translate t F)) =
        mu • physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S R.reflectionData halfExtent N hN beta hbeta
                R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
                R.approximatingReflectionInvariantFamily n).carrierOfPositiveTime F)) :
    let P := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n
    C.finiteOperator n t (P.physicalState (P.carrierOfPositiveTime F)) =
      mu • P.physicalState (P.carrierOfPositiveTime F) := by
  apply R.finiteOperator_on_positiveTimeObservable_of_pairMoment_eigen C n t F mu
  rw [hMoment]
  simp

/-- Time-one specialization: a scaling law for the actual canonical Wilson
boundary moment of one positive-time observable produces the exact bounded
one-step eigen-equation required by the continuum common-carrier theorem. -/
theorem finiteOperator_one_on_positiveTimeObservable_of_boundaryMoment_eigen
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ) (F : R.reflectionData.positiveTimeSubalgebra) (mu : ℝ)
    (hMoment :
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S R.reflectionData halfExtent N hN beta hbeta
                R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
                R.approximatingReflectionInvariantFamily n).carrierOfPositiveTime
                  (C.translate 1 F)) =
        mu • physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S R.reflectionData halfExtent N hN beta hbeta
                R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
                R.approximatingReflectionInvariantFamily n).carrierOfPositiveTime F)) :
    let P := physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n
    C.finiteOperator n 1 (P.physicalState (P.carrierOfPositiveTime F)) =
      mu • P.physicalState (P.carrierOfPositiveTime F) := by
  exact R.finiteOperator_on_positiveTimeObservable_of_boundaryMoment_eigen
    C n 1 F mu hMoment

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
