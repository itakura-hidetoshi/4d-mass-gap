import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentFiniteEigenmode
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance osBoundaryExcitationObservableImageSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A one-particle endpoint-pair mode: the primary endpoint carries `f`, while
`omega` is the companion top/vacuum endpoint vector.

Keeping the two factors explicit is important.  The one-particle route needs a
transfer-fixed companion mode, not a second excitation; otherwise the finite
transfer eigenvalue would be squared. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
    (H N : ℕ)
    (f omega : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor f omega

/-- The same endpoint-pair construction after one transfer step, with both
endpoint vectors supplied explicitly. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
    (H N : ℕ)
    (fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor fOne omegaOne

/-- If the primary endpoint scales by `mu` and the companion endpoint is fixed,
the genuine two-endpoint one-step pair scales by exactly `mu`, not `mu^2`. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2_eq_smul
    (H N : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (mu : ℝ)
    (hf : fOne = mu • f)
    (homega : omegaOne = omega) :
    periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
        H N fOne omegaOne =
      mu • periodicHypercubicEvenSpecialUnitaryOneSidedPairL2 H N f omega := by
  rw [hf, homega]
  unfold periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
  unfold periodicHypercubicEvenSpecialUnitaryOneSidedPairL2
  exact realL2ExternalTensor_smul_left mu f omega

/-- Pull a one-particle endpoint-pair vector back to the genuine shared Wilson
reflection boundary. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
    (H N : ℕ)
    (f omega : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N :=
  periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
    (periodicHypercubicEvenSpecialUnitaryOneSidedPairL2 H N f omega)

/-- Pull the one-step endpoint-pair vector back to the same genuine Wilson
boundary carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
    (H N : ℕ)
    (fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N :=
  periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
    (periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2
      H N fOne omegaOne)

/-- Boundary reindexing is linear, so the one-particle eigenvalue survives
unchanged on the actual reflection-fixed Wilson boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2_eq_smul
    (H N : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (mu : ℝ)
    (hf : fOne = mu • f)
    (homega : omegaOne = omega) :
    periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        H N fOne omegaOne =
      mu • periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2 H N f omega := by
  unfold periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
  unfold periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
  rw [periodicHypercubicEvenSpecialUnitaryOneSidedPairOneStepL2_eq_smul
    H N f omega fOne omegaOne mu hf homega]
  simp

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Exact observable-image datum for a one-sided endpoint mode at one cutoff.

The same positive-time observable realizes the initial one-particle boundary
vector and, after observable translation by one unit, the supplied one-step
endpoint vector.  This package asserts no surjectivity or richness theorem for
the positive-time algebra. -/
structure OneSidedBoundaryObservableImageAt
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) N)) where
  observable : R.reflectionData.positiveTimeSubalgebra
  momentZero :
    R.canonicalBoundaryMomentAt n
        ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime observable) =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryL2
        (halfExtent n) N f omega
  momentOne :
    R.canonicalBoundaryMomentAt n
        ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime
          (C.translate 1 observable)) =
      periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2
        (halfExtent n) N fOne omegaOne

/-- A translation-compatible observable image of a one-particle endpoint mode
is an exact finite Wilson OS eigenvector whenever the primary endpoint scales
by `mu` and the companion endpoint is fixed.

The physical transfer specialization will supply these two endpoint equations;
this theorem is independent of that transfer module so the actual OS boundary
and transfer import graphs remain separated until their instance diamond is
made coherent. -/
theorem finiteOperator_one_eigen_of_oneSidedBoundaryObservableImage
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ)
    (f omega fOne omegaOne : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
        (halfExtent n) N))
    (mu : ℝ)
    (hf : fOne = mu • f)
    (homega : omegaOne = omega)
    (W : OneSidedBoundaryObservableImageAt
      R C n f omega fOne omegaOne) :
    C.finiteOperator n 1
        ((R.approximatingPreHilbertDataAt n).physicalState
          ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime W.observable)) =
      mu • (R.approximatingPreHilbertDataAt n).physicalState
        ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime W.observable) := by
  apply R.finiteOperator_one_on_positiveTimeObservable_of_boundaryMoment_eigen
    C n W.observable mu
  rw [W.momentOne, W.momentZero]
  exact
    periodicHypercubicEvenSpecialUnitaryOneSidedBoundaryOneStepL2_eq_smul
      (halfExtent n) N f omega fOne omegaOne mu hf homega

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
