import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateProductHaar
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixSpatialConditionalExpectation
import Mathlib.Tactic

/-!
# Beta-zero pair-Haar carrier and six-spatial coordinate projections

At beta = 0 the genuine ground-state joint law is exactly pair Haar.  This
module exposes the corresponding literal pair-Haar L2 carrier and the six
coordinate/color conditional-expectation projections on that carrier.

The key design point is to keep the product-Haar operator definitions on their
literal measure carrier.  The canonical ground-state beta-zero L2 carrier is
identified with that carrier by a small type-equality theorem, rather than by
rewriting a proof-indexed Lp type inside every continuous-linear-map
definition.  This avoids expensive dependent elaboration and leaves operator
transport to the next, dedicated theorem unit.

No commutation statement is made here.
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

/-- Literal pair-Haar real L2 carrier for two spatial slices. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
    (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- The canonical beta-zero ground-state joint L2 carrier is the literal
pair-Haar L2 carrier.  This is the type-level form of the exact measure theorem
from the preceding unit. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2_zero_eq_pairHaarL2
    (H N : ℕ)
    (hN : 0 < N) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num) =
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
        H N := by
  unfold
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
      H N hN]

/-- Literal pair-Haar orthogonal projection which forgets one right-boundary
spatial color. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  (Submodule.subtypeL
    (lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N))).comp
    (condExpL2 ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
        H N color))

/-- The six literal pair-Haar spatial projections, indexed by Fin 6. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
    (H N : ℕ) :
    Fin 6 →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  fun c =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorPairHaarProjection
      H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

end

end MGAP4D.MathlibAnalytic
