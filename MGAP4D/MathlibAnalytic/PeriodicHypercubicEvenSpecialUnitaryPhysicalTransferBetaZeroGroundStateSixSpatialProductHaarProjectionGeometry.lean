import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarProjection
import Mathlib.Tactic

/-!
# Geometry of the beta-zero six-spatial pair-Haar projections

The preceding unit exposes the six genuine spatial-color conditional
expectations on the literal beta-zero pair-Haar `L²` carrier.

This file records the two Hilbert-projection properties needed by the finite
commuting-projection tensorization theorem:

* every color projection is idempotent;
* every color projection is symmetric/self-adjoint in the real inner product.

No pairwise commutation is asserted here.  After this unit, commutation is the
only remaining projection-algebra input for specializing the abstract
tensorization theorem to the genuine beta-zero six-spatial family.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroSixSpatialProductHaarProjectionGeometryTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroSixSpatialProductHaarProjectionGeometryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroSixSpatialProductHaarProjectionGeometrySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroSixSpatialProductHaarProjectionGeometryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroSixSpatialProductHaarProjectionGeometryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroSixSpatialProductHaarProjectionGeometrySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal application formula for one pair-Haar spatial-color projection. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_apply
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
        H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
        H N color f =
      (condExpL2 ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
          H N color) f :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
          H N) := by
  rfl

/-- Each literal pair-Haar spatial-color conditional expectation is
idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_idempotent
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
      H N color).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
        H N color) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
      H N color := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_apply]
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
      H N color
  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨hm⟩
  let q : lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
    condExpL2 ℝ ℝ hm f
  change
    ((condExpL2 ℝ ℝ hm
      (q :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
          H N) :
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
        H N) = q
  have hq :
      (condExpL2 ℝ ℝ hm
        (q :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
            H N) :
        lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
            H N color) 2
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  exact congrArg
    (fun x : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) =>
      (x :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
          H N)) hq

/-- Each literal pair-Haar spatial-color conditional expectation is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_symmetric
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
      H N color :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N).IsSymmetric := by
  intro f g
  change
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
          H N color f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
          H N color g)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_apply]
  exact inner_condExpL2_left_eq_right
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
      H N color)

/-- Every member of the six-spatial pair-Haar family is idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
    (H N : ℕ)
    (c : Fin 6) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
      H N c).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
      H N c := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_idempotent
      H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

/-- Every member of the six-spatial pair-Haar family is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
    (H N : ℕ)
    (c : Fin 6) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
      H N c :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N).IsSymmetric := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection_symmetric
      H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

end

end MGAP4D.MathlibAnalytic
