import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixSpatialCoordinateElimination
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance groundStateJointSpatialCoordinateMeasurableEquivMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Repackage the two spatial-boundary configurations as one function on the
literal disjoint union of left and right link coordinates.  This is a genuine
measurable equivalence, so no information or measurable structure is lost. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
    (H N : ℕ) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ≃ᵐ
      (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi
    (fun _ : PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H =>
      Matrix.specialUnitaryGroup (Fin N) ℂ)).symm

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inl
    (H N : ℕ)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N z (Sum.inl e) = z.1 e := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv_apply_inr
    (H N : ℕ)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N z (Sum.inr e) = z.2 e := by
  rfl

/-- Restrict the unified joint coordinate presentation to the coordinates
retained by one right-boundary color update. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun z i =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N z i.1

/-- The right retained-coordinate restriction is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
        H N c) := by
  rw [measurable_pi_iff]
  intro i
  exact
    (measurable_pi_apply i.1).comp
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N).measurable

/-- Restrict the unified joint coordinate presentation to the coordinates
retained by one left-boundary color update. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
    (H N : ℕ)
    (c : Fin 6) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      (periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  fun z i =>
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
      H N z i.1

/-- The left retained-coordinate restriction is measurable. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
    (H N : ℕ)
    (c : Fin 6) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
        H N c) := by
  rw [measurable_pi_iff]
  intro i
  exact
    (measurable_pi_apply i.1).comp
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N).measurable

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction_inl
    (H N : ℕ)
    (c : Fin 6)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
        H N c z
        ⟨Sum.inl e, by
          simp [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet]⟩ =
      z.1 e := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction_inr
    (H N : ℕ)
    (c : Fin 6)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
        H N c z
        ⟨Sum.inr e, by
          simp [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet]⟩ =
      z.2 e := by
  rfl

end

end MathlibAnalytic
end MGAP4D
