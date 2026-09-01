import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentFiniteEigenmode
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance osBoundaryExcitationObservableImageSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A one-particle transfer mode is placed on the primary endpoint while the
antipodal endpoint is kept in the chosen normalized top mode.

This is deliberately not the excitation tensor square `K ⊗ K`: the second
factor is a transfer-fixed top mode.  Consequently an eigenvalue `mu` on the
first factor remains `mu`, rather than being doubled to `mu^2`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))

/-- Evolve both endpoints by one normalized physical one-slab transfer before
forming the endpoint-pair mode.  The second factor will collapse back to the
top mode by the finite-volume vacuum-fixed theorem. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensor
    (((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- The antipodal top factor is transfer-fixed, so the genuine two-endpoint
one-step mode is exactly the static one-sided pair built from the transferred
primary mode. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairL2
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) f) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairL2
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed]

/-- Hence an exact one-slice eigenmode with eigenvalue `mu` becomes a genuine
one-particle pair mode with the same eigenvalue, not its square. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2_eq_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta f = mu • f) :
    periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2
        H N hN beta hbeta f =
      mu • periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairL2
        H N hN beta hbeta f := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2_eq]
  rw [hf]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairL2
  rw [realL2ExternalTensor_smul_left]

/-- Pull the one-particle endpoint-pair mode back to the genuine shared Wilson
reflection boundary. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N :=
  periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairL2
      H N hN beta hbeta f)

/-- The corresponding boundary vector after evolving both endpoints for one
normalized physical transfer step. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryOneStepL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N :=
  periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2
      H N hN beta hbeta f)

/-- Boundary reindexing is linear, so the same exact one-particle eigenvalue
survives on the actual reflection-fixed Wilson boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryOneStepL2_eq_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (mu : ℝ)
    (hf : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta f = mu • f) :
    periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryOneStepL2
        H N hN beta hbeta f =
      mu • periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryL2
        H N hN beta hbeta f := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryOneStepL2
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryL2
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalModeTopPairOneStepL2_eq_smul
    H N hN beta hbeta f mu hf]
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

/-- Exact remaining observable-image datum for one finite one-particle mode.

The same positive-time observable must realize the one-sided physical boundary
mode at time zero and, after the already-given observable translation, the
boundary mode obtained by evolving both physical endpoints for one normalized
one-slab step.  No surjectivity of the positive-time algebra is asserted. -/
structure PhysicalModeTopBoundaryObservableImageAt
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
      (halfExtent n) N) where
  observable : R.reflectionData.positiveTimeSubalgebra
  momentZero :
    R.canonicalBoundaryMomentAt n
        ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime observable) =
      periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryL2
        (halfExtent n) N hN (beta n) (hbeta n) f
  momentOne :
    R.canonicalBoundaryMomentAt n
        ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime
          (C.translate 1 observable)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryOneStepL2
        (halfExtent n) N hN (beta n) (hbeta n) f

/-- Once the exact observable-image square is supplied, a genuine one-slice
physical transfer eigenmode becomes an exact eigenvector of the actual finite
Wilson OS time-one operator.  This feeds directly into the canonical
finite-to-continuum common-carrier theorem. -/
theorem finiteOperator_one_eigen_of_physicalModeTopBoundaryObservableImage
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
    (W : PhysicalModeTopBoundaryObservableImageAt R C n f) :
    C.finiteOperator n 1
        ((R.approximatingPreHilbertDataAt n).physicalState
          ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime W.observable)) =
      mu • (R.approximatingPreHilbertDataAt n).physicalState
        ((R.approximatingPreHilbertDataAt n).carrierOfPositiveTime W.observable) := by
  apply R.finiteOperator_one_on_positiveTimeObservable_of_boundaryMoment_eigen
    C n W.observable mu
  rw [W.momentOne, W.momentZero]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalModeTopBoundaryOneStepL2_eq_smul
      (halfExtent n) N hN (beta n) (hbeta n) f mu hf

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
