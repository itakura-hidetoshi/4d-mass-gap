import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialPairHaarRetainedMeasurability
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite color index of the unique six-color block containing a spatial
slice link.  This is the coordinate that is omitted when that same color is
updated. -/
def periodicHypercubicEvenSpatialSliceLinkOmittedColorIndex
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : Fin 6 :=
  periodicHypercubicEvenGroundStateSpatialColorEquivFin
    (periodicHypercubicEvenSpatialSliceLinkColor H e)

@[simp] theorem
    periodicHypercubicEvenGroundStateSpatialColorEquivFin_symm_omittedColorIndex
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm
        (periodicHypercubicEvenSpatialSliceLinkOmittedColorIndex H e) =
      periodicHypercubicEvenSpatialSliceLinkColor H e := by
  simp [periodicHypercubicEvenSpatialSliceLinkOmittedColorIndex]

/-- Intersecting the six off-color spatial-link supports leaves no link.  Every
spatial link is removed by the unique update whose color is the link's own
color. -/
theorem periodicHypercubicEvenSpatialSliceOffColorSet_iInter_eq_empty
    (H : ℕ) :
    (⋂ c : Fin 6,
      {e : PeriodicHypercubicEvenSpatialSliceLink H |
        periodicHypercubicEvenSpatialSliceLinkColor H e ≠
          periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c}) = ∅ := by
  ext e
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  exact
    (h (periodicHypercubicEvenSpatialSliceLinkOmittedColorIndex H e))
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin_symm_omittedColorIndex H e)

/-- Coordinate carrier for the two spatial boundaries of one slab.  `Sum.inl`
labels left-boundary links and `Sum.inr` labels right-boundary links. -/
abbrev PeriodicHypercubicEvenGroundStateJointSpatialCoordinate (H : ℕ) : Type :=
  Sum
    (PeriodicHypercubicEvenSpatialSliceLink H)
    (PeriodicHypercubicEvenSpatialSliceLink H)

/-- Coordinates retained by a right-boundary color update: every left
coordinate and every right coordinate outside the updated color. -/
def periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet
    (H : ℕ)
    (c : Fin 6) :
    Set (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  {i | match i with
    | Sum.inl _ => True
    | Sum.inr e =>
        periodicHypercubicEvenSpatialSliceLinkColor H e ≠
          periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c}

/-- Coordinates retained by a left-boundary color update: every right
coordinate and every left coordinate outside the updated color. -/
def periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet
    (H : ℕ)
    (c : Fin 6) :
    Set (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  {i | match i with
    | Sum.inl e =>
        periodicHypercubicEvenSpatialSliceLinkColor H e ≠
          periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c
    | Sum.inr _ => True}

/-- Literal left-boundary coordinate support in the joint coordinate carrier. -/
def periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet
    (H : ℕ) :
    Set (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  {i | match i with
    | Sum.inl _ => True
    | Sum.inr _ => False}

/-- Literal right-boundary coordinate support in the joint coordinate carrier. -/
def periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet
    (H : ℕ) :
    Set (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  {i | match i with
    | Sum.inl _ => False
    | Sum.inr _ => True}

/-- The six right-update retained coordinate supports intersect exactly in the
left boundary.  This is the finite combinatorial core of
`right six fixed -> left-boundary measurable`. -/
theorem
    periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet_iInter_eq_leftBoundary
    (H : ℕ) :
    (⋂ c : Fin 6,
      periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c) =
      periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H := by
  ext i
  cases i with
  | inl e =>
      simp [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet,
        periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet]
  | inr e =>
      simp only [Set.mem_iInter,
        periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet,
        periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet,
        Set.mem_setOf_eq]
      constructor
      · intro h
        exact
          (h (periodicHypercubicEvenSpatialSliceLinkOmittedColorIndex H e))
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin_symm_omittedColorIndex H e)
      · intro h
        exact False.elim h

/-- Symmetrically, the six left-update retained coordinate supports intersect
exactly in the right boundary. -/
theorem
    periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet_iInter_eq_rightBoundary
    (H : ℕ) :
    (⋂ c : Fin 6,
      periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c) =
      periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H := by
  ext i
  cases i with
  | inl e =>
      simp only [Set.mem_iInter,
        periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet,
        periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet,
        Set.mem_setOf_eq]
      constructor
      · intro h
        exact
          (h (periodicHypercubicEvenSpatialSliceLinkOmittedColorIndex H e))
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin_symm_omittedColorIndex H e)
      · intro h
        exact False.elim h
  | inr e =>
      simp [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet,
        periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet]

end

end MathlibAnalytic
end MGAP4D
