import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorPlaquetteSeparation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonBoundaryEightColorGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two actual spatial-slice links of the same canonical six-color that both
occur on one four-dimensional Wilson plaquette are the same spatial link.

This is the exact descent of eight-color plaquette separation to the six-color
carrier used by the ground-state spatial conditional expectations. -/
theorem periodicHypercubicEvenSpatialSliceLink_sameColor_touches_eq
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (he : periodicHypercubicPlaquetteTouchesEdge
      (PeriodicHypercubicEvenSideLength H) p
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H e))
    (hf : periodicHypercubicPlaquetteTouchesEdge
      (PeriodicHypercubicEvenSideLength H) p
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H f))
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f) :
    e = f := by
  have hEdgeColor :
      periodicHypercubicEvenEdgeColor H
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) =
        periodicHypercubicEvenEdgeColor H
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) := by
    simpa only [periodicHypercubicEvenEdgeColor_spatialSliceLinkEmbedding] using
      congrArg periodicHypercubicEvenSpatialBoundaryColorEmbedding hColor
  have hEmbed :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H e =
        periodicHypercubicEvenSpatialSliceLinkEmbedding H f :=
    periodicHypercubicEvenPlaquette_sameColor_touches_eq
      H p he hf hEdgeColor
  exact periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H hEmbed

/-- Distinct actual spatial-slice links in one of the six ground-state spatial
color classes never share a Wilson plaquette.  The statement is uniform in the
finite side length and introduces no analytic or probabilistic hypothesis. -/
theorem periodicHypercubicEvenSpatialSliceLink_sameColor_no_common_plaquette
    (H : ℕ)
    {e f : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H e =
      periodicHypercubicEvenSpatialSliceLinkColor H f)
    (hne : e ≠ f) :
    ¬ ∃ p : PeriodicHypercubicEvenPlaquette H,
      periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H e) ∧
        periodicHypercubicPlaquetteTouchesEdge
          (PeriodicHypercubicEvenSideLength H) p
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H f) := by
  rintro ⟨p, he, hf⟩
  exact hne
    (periodicHypercubicEvenSpatialSliceLink_sameColor_touches_eq
      H p he hf hColor)

end

end MathlibAnalytic
end MGAP4D
