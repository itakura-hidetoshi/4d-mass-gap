import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonVacuumL2LinearIsometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorEdgeMatching
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

/-- The six colors visible on one spatial boundary: three non-time coordinate
directions times the two checkerboard parities.  We keep the direction as a
subtype rather than renumbering the colors, so the map back to the canonical
four-dimensional eight-color set is literal. -/
abbrev PeriodicHypercubicEvenSpatialBoundaryColor : Type :=
  PeriodicHypercubicEvenSpatialDirection × ZMod 2

/-- Embed a spatial-boundary color into the canonical four-dimensional
Wilson eight-color set. -/
def periodicHypercubicEvenSpatialBoundaryColorEmbedding
    (c : PeriodicHypercubicEvenSpatialBoundaryColor) :
    PeriodicHypercubicEvenEdgeColor :=
  (c.1.1, c.2)

/-- The spatial-boundary color embedding loses no color information. -/
theorem periodicHypercubicEvenSpatialBoundaryColorEmbedding_injective :
    Function.Injective periodicHypercubicEvenSpatialBoundaryColorEmbedding := by
  intro c d h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun x : PeriodicHypercubicEvenEdgeColor => x.1) h
  · exact congrArg (fun x : PeriodicHypercubicEvenEdgeColor => x.2) h

/-- A color is visible on the spatial boundary exactly when its direction is
not the time direction `0`.  Thus the canonical eight colors split without
renumbering into six spatial colors and the two temporal colors. -/
theorem periodicHypercubicEvenSpatialBoundaryColor_mem_range_iff_axis_ne_zero
    (c : PeriodicHypercubicEvenEdgeColor) :
    c ∈ Set.range periodicHypercubicEvenSpatialBoundaryColorEmbedding ↔
      c.1 ≠ 0 := by
  constructor
  · rintro ⟨d, rfl⟩
    exact d.1.2
  · intro hc
    refine ⟨(⟨c.1, hc⟩, c.2), ?_⟩
    exact Prod.ext rfl rfl

/-- The canonical boundary color of one spatial-slice link. -/
def periodicHypercubicEvenSpatialSliceLinkColor
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpatialBoundaryColor :=
  (e.2, periodicHypercubicEvenCheckerboardParity H e.1.1)

/-- Coloring a spatial link after embedding it into the physical positive-link
carrier agrees literally with embedding its six-color boundary color into the
canonical eight-color set. -/
@[simp]
theorem periodicHypercubicEvenEdgeColor_spatialSliceLinkEmbedding
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenEdgeColor H
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
      periodicHypercubicEvenSpatialBoundaryColorEmbedding
        (periodicHypercubicEvenSpatialSliceLinkColor H e) := by
  rfl

/-- Every embedded spatial-slice link has non-time color direction. -/
theorem periodicHypercubicEvenEdgeColor_spatialSliceLinkEmbedding_axis_ne_zero
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenEdgeColor H
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H e)).1 ≠ 0 := by
  exact e.2.2

/-- Neither of the two temporal Wilson colors occurs among spatial-boundary
links.  These are precisely the two colors whose boundary descent is empty. -/
theorem periodicHypercubicEvenSpatialSliceLinkColor_ne_temporal
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (parity : ZMod 2) :
    periodicHypercubicEvenEdgeColor H
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) ≠
      ((0 : PeriodicHypercubicAxis), parity) := by
  intro h
  have haxis := congrArg Prod.fst h
  exact e.2.2 haxis

/-- Equivalently, there is no spatial-slice link carrying either temporal
color `(0, parity)`. -/
theorem periodicHypercubicEven_no_spatialSliceLink_of_temporalColor
    (H : ℕ)
    (parity : ZMod 2) :
    ¬ ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenEdgeColor H
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
        ((0 : PeriodicHypercubicAxis), parity) := by
  rintro ⟨e, he⟩
  exact periodicHypercubicEvenSpatialSliceLinkColor_ne_temporal H e parity he

/-- Every actual boundary-link color lies in the six-color spatial image. -/
theorem periodicHypercubicEven_spatialSliceLinkColor_mem_boundaryRange
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenEdgeColor H
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) ∈
      Set.range periodicHypercubicEvenSpatialBoundaryColorEmbedding := by
  exact ⟨periodicHypercubicEvenSpatialSliceLinkColor H e, by simp⟩

end

end MathlibAnalytic
end MGAP4D
