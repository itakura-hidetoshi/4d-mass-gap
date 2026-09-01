import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryExcitationObservableImage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance osPhysicalTransferModeObservableImageSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osPhysicalTransferModeObservableImageSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Forget the gauge-invariant one-slice subtype and view a physical transfer
mode in the ambient real Haar-`L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
    (H N : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Ambient Haar-`L²` representative of the normalized one-step physical
transfer of a gauge-invariant one-slice mode. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta f :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Ambient Haar-`L²` representative of the chosen normalized top/vacuum
one-slice transfer mode. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- Ambient Haar-`L²` representative of the normalized one-step transfer of
the chosen top/vacuum mode. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- A normalized physical one-slice eigen-equation descends through the subtype
coercion to the ambient Haar-`L²` endpoint equation required by the one-sided
Wilson boundary construction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_eq_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta f = mu • f) :
    periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
        H N hN beta hbeta f =
      mu • periodicHypercubicEvenSpecialUnitaryPhysicalModeLp H N f := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
  simpa using congrArg
    (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
      (z : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) hf

/-- The companion top/vacuum endpoint is fixed after forgetting the
one-slice gauge-invariant subtype. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
        H N hN beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
  simpa using congrArg
    (fun z : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N =>
      (z : Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H N hN beta hbeta)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Observable-image datum specialized to the actual normalized physical
one-slice transfer and its fixed top/vacuum companion endpoint. -/
abbrev PhysicalTransferModeBoundaryObservableImageAt
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N) :=
  OneSidedBoundaryObservableImageAt R C n
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
      (halfExtent n) N f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      (halfExtent n) N hN (beta n) (hbeta n))
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n) f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n))

/-- A genuine eigenmode of the normalized one-slice physical transfer becomes
an exact eigenvector of the actual completed finite Wilson OS time-one operator
as soon as its one-sided boundary mode is realized by one positive-time
observable and its unit translate.

The top endpoint contributes eigenvalue one, so the physical eigenvalue `mu`
is preserved exactly.  This theorem is the finite-model input expected by the
common-carrier finite-to-continuum theorem. -/
theorem finiteOperator_one_eigen_of_normalizedPhysicalTransferModeObservableImage
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n) f = mu • f)
    (W : PhysicalTransferModeBoundaryObservableImageAt R C n f) :
    C.finiteOperator n 1
        ((R.approximatingPreHilbertDataAt n).physicalState
          ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime W.observable)) =
      mu • (R.approximatingPreHilbertDataAt n).physicalState
        ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime W.observable) := by
  apply finiteOperator_one_eigen_of_oneSidedBoundaryObservableImage
    R C n
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeLp
      (halfExtent n) N f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeLp
      (halfExtent n) N hN (beta n) (hbeta n))
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n) f)
    (periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp
      (halfExtent n) N hN (beta n) (hbeta n))
    mu
  · exact periodicHypercubicEvenSpecialUnitaryPhysicalModeOneStepLp_eq_smul
      (halfExtent n) N hN (beta n) (hbeta n) f mu hf
  · exact periodicHypercubicEvenSpecialUnitaryPhysicalTopModeOneStepLp_eq
      (halfExtent n) N hN (beta n) (hbeta n)

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
