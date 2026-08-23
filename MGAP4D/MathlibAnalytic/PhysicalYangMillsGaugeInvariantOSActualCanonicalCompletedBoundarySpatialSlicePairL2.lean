import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalCompletedBoundaryClosedSubspace
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySpatialSlicePair
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance completedBoundaryPairL2SideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance completedBoundaryPairL2SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance completedBoundaryPairL2SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance completedBoundaryPairL2SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance completedBoundaryPairL2SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance completedBoundaryPairL2SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance completedBoundaryPairL2SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The boundary-side one-slice Haar definition from the reflection-fixed
coordinate decomposition is exactly the one-slice Haar definition used by the
actual one-slab transfer construction. -/
@[simp] theorem periodicHypercubicEvenBoundarySpatialSliceHaarMeasure_eq_oneSlab
    (H N : ℕ) :
    periodicHypercubicEvenBoundarySpatialSliceHaarMeasure H N =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N :=
  rfl

/-- Hence the two-boundary Haar law produced by the reflection-fixed boundary
classification is literally the actual one-slab pair-Haar law. -/
@[simp] theorem periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure_eq_oneSlab
    (H N : ℕ) :
    periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure H N =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N :=
  rfl

/-- The canonical shared-boundary coordinate equivalence preserves the exact
pair-Haar measure used by the actual Wilson one-slab kernel. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  simpa only [periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure_eq_oneSlab]
    using
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar
        H N)

/-- The inverse coordinate equivalence is measure-preserving in the direction
needed to pull shared-boundary `L²` vectors onto the actual one-slab pair
carrier. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_measurePreserving_oneSlabHaar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
  MeasurePreserving.symm
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
      H N)

/-- Real pair-Haar `L²` carrier on the two modern spatial slices.  This is the
ambient Hilbert space containing the actual one-slab kernel vector. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2
    (H N : ℕ) : Type :=
  MeasureTheory.Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- Pull a shared-boundary `L²` vector through the inverse two-slice coordinate
equivalence.  Mathlib's measure-preserving `Lp` pullback gives norm preservation
canonically, so no separate analytic estimate is introduced here. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2 H N :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_measurePreserving_oneSlabHaar
      H N)

/-- The transported `L²` class is represented almost everywhere by literal
composition with the inverse boundary-to-two-slice coordinate equivalence. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2_coeFn
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N) :
    periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2 H N f =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      f ∘
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm := by
  change MeasureTheory.Lp.compMeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_measurePreserving_oneSlabHaar
        H N) f =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      f ∘
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_measurePreserving_oneSlabHaar
      H N)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- The completed actual Wilson OS Hilbert space embeds isometrically into the
same two-spatial-boundary pair-Haar `L²` carrier on which the actual one-slab
Wilson kernel vector is defined.  This is a carrier identification only; it
does not identify the OS time-translation operator with the one-slab transfer. -/
noncomputable def toCompletedSpatialSlicePairMomentLinearIsometryAutomatic
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2 (halfExtent n) N :=
  (periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2
      (halfExtent n) N).comp
    (R.toCompletedBoundaryMomentLinearIsometryAutomatic n)

/-- On dense physical states, the pair-Haar realization is exactly the
canonical Wilson boundary moment from #2051 followed by the canonical
boundary-to-two-slice `L²` transport. -/
@[simp] theorem toCompletedSpatialSlicePairMomentLinearIsometryAutomatic_physicalState
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent N hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).Carrier) :
    R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n).physicalState F) =
      periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2
        (halfExtent n) N
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S R.reflectionData halfExtent N hN beta hbeta
            R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
            R.approximatingReflectionInvariantFamily n F) := by
  simp [toCompletedSpatialSlicePairMomentLinearIsometryAutomatic]

/-- The transported completed OS image remains closed in the actual one-slab
pair-Haar `L²` carrier because its domain is complete and the transport is a
linear isometry. -/
theorem isClosed_range_toCompletedSpatialSlicePairMomentLinearIsometryAutomatic
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ) :
    IsClosed
      (Set.range (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n)) :=
  (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n).isometry
    |>.isClosedEmbedding.isClosed_range

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
