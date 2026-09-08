import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedTwelveSpatialConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

set_option maxHeartbeats 1000000

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A vector fixed by one genuine right-boundary color conditional expectation
belongs to the corresponding retained-information `L²` subspace.  This is the
range geometry of the actual conditional expectation, not an abstract
projection hypothesis. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_mem_lpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color z = z) :
    z ∈ lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace_le
      H N color
  let q : lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
    condExpL2 ℝ ℝ hm z
  have hq :
      (q : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) = z := by
    simpa [q, hm] using hz
  rw [← hq]
  exact q.property

/-- The left-boundary counterpart: a vector fixed by one genuine left color
conditional expectation belongs to that left-color retained-information
subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_fixed_mem_lpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
        H N hN beta hbeta color z = z) :
    z ∈ lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
      H N color
  let q : lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
    condExpL2 ℝ ℝ hm z
  have hq :
      (q : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) = z := by
    simpa [q, hm] using hz
  rw [← hq]
  exact q.property

/-- The intersection of all six right-update retained `L²` subspaces.  A point
of this submodule is simultaneously measurable with respect to every sigma
algebra retaining the full left boundary and all right coordinates outside one
spatial color. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Submodule ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :=
  ⨅ c : Fin 6,
    lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)

/-- The corresponding intersection for all six left-update retained `L²`
subspaces. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Submodule ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :=
  ⨅ c : Fin 6,
    lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)

/-- Every vector fixed by all twelve genuine spatial conditional expectations
lies simultaneously in the six right retained-information ranges and the six
left retained-information ranges.  The remaining common-fixed problem is now
purely the identification of these two concrete intersections. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_mem_rightSix_leftSix_retained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hfixed :
      ∀ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
          H N hN beta hbeta c z = z) :
    z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
          H N hN beta hbeta ∧
      z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
          H N hN beta hbeta := by
  have hsplit :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff
      H N hN beta hbeta z).1 hfixed
  constructor
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas]
    rw [Submodule.mem_iInf]
    intro c
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2_fixed_mem_lpMeas
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z
        (hsplit.1 c)
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas]
    rw [Submodule.mem_iInf]
    intro c
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_fixed_mem_lpMeas
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) z
        (hsplit.2 c)

end

end MathlibAnalytic
end MGAP4D
