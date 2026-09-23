import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateProductHaar
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixSpatialConditionalExpectation
import Mathlib.Tactic

/-!
# Beta-zero six-spatial ground-state projections are product-Haar projections

At beta = 0 the genuine ground-state joint law is exactly pair Haar.  This
module makes that measure identity visible at the operator level.

For one spatial color we define the corresponding conditional-expectation
orthogonal projection using pair Haar literally as the measure argument.  The
target type is transported back to the canonical beta-zero ground-state joint
L2 carrier through the already-proved exact measure equality.  We then identify
the genuine Wilson ground-state conditional expectation with this product-Haar
projection, first colorwise and then as the full Fin 6 family.

No commutation statement is made here.  Pairwise commutation is the next
product-Haar/Fubini unit.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

local instance betaZeroSixSpatialProductHaarProjectionTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroSixSpatialProductHaarProjectionCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroSixSpatialProductHaarProjectionSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroSixSpatialProductHaarProjectionMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroSixSpatialProductHaarProjectionBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroSixSpatialProductHaarProjectionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal pair-Haar conditional-expectation projection which forgets one
right-boundary spatial color, transported to the canonical beta-zero
ground-state joint L2 carrier by the exact equality of measures. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorProductHaarProjection_zero
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num) →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN]
  exact
    (Submodule.subtypeL
      (lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))).comp
      (condExpL2 ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
          H N color))

/-- At beta = 0 the genuine one-color Wilson ground-state conditional
expectation is exactly the corresponding literal pair-Haar projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_zero_eq_productHaarProjection
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN 0 (by norm_num) color =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorProductHaarProjection_zero
        H N hN color := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorProductHaarProjection_zero
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN]

/-- The literal pair-Haar six-spatial projection family, indexed by Fin 6. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialProductHaarProjection_zero
    (H N : ℕ)
    (hN : 0 < N) :
    Fin 6 →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN 0 (by norm_num) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN 0 (by norm_num) :=
  fun c =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorProductHaarProjection_zero
      H N hN
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

/-- The whole genuine beta-zero six-spatial conditional-expectation family is
the literal product-Haar family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_zero_eq_productHaarProjection
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        H N hN 0 (by norm_num) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialProductHaarProjection_zero
        H N hN := by
  funext c
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_zero_eq_productHaarProjection
      H N hN
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

end

end MGAP4D.MathlibAnalytic
