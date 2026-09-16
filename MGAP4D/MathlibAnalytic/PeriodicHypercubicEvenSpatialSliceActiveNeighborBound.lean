import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRemoteSlabCancellation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance spatialSliceActiveNeighborBoundEvenSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance spatialSliceActiveNeighborBoundSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Intrinsic spatial links that can interact directly with `target` through a
single spatial Wilson plaquette.  The diagonal is removed explicitly. -/
noncomputable def periodicHypercubicEvenSpatialSliceActiveNeighbors
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.filter fun source =>
    source ≠ target ∧
      periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source

@[simp] theorem periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target ↔
      source ≠ target ∧
        periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source := by
  classical
  simp [periodicHypercubicEvenSpatialSliceActiveNeighbors]

/-- Every intrinsic spatial active neighbor embeds into the already-formalized
four-dimensional periodic active-neighbor set. -/
theorem periodicHypercubicEvenSpatialSliceActiveNeighbors_embedding_subset
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSliceActiveNeighbors H target).image
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H) ⊆
      periodicHypercubicActiveNeighbors
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  classical
  intro fullSource hFullSource
  rcases Finset.mem_image.mp hFullSource with ⟨source, hSource, rfl⟩
  have hActive :=
    (periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff
      H target source).mp hSource
  rcases hActive with ⟨hDistinct, p, hTargetTouches, hSourceTouches⟩
  let fullTarget := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let fullSource := periodicHypercubicEvenSpatialSliceLinkEmbedding H source
  let fullP := periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p
  have hTargetTouchesFull :
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H) fullP fullTarget := by
    exact hTargetTouches
  have hSourceTouchesFull :
      periodicHypercubicPlaquetteTouchesEdge
        (PeriodicHypercubicEvenSideLength H) fullP fullSource := by
    exact hSourceTouches
  have hFullDistinct : fullSource ≠ fullTarget := by
    intro hEq
    exact hDistinct
      (periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H hEq)
  have hPTouching :
      fullP ∈ periodicHypercubicTouchingPlaquettes
        (PeriodicHypercubicEvenSideLength H) fullTarget :=
    (periodicHypercubic_mem_touchingPlaquettes_iff
      (PeriodicHypercubicEvenSideLength H) fullTarget fullP).mpr hTargetTouchesFull
  have hSourceEdge :
      fullSource ∈ periodicHypercubicPlaquetteEdges
        (PeriodicHypercubicEvenSideLength H) fullP :=
    periodicHypercubic_mem_plaquetteEdges_of_touches
      (PeriodicHypercubicEvenSideLength H) fullP fullSource hSourceTouchesFull
  have hSourceOther :
      fullSource ∈ periodicHypercubicPlaquetteOtherEdges
        (PeriodicHypercubicEvenSideLength H) fullTarget fullP := by
    simp [periodicHypercubicPlaquetteOtherEdges, hSourceEdge, hFullDistinct]
  unfold periodicHypercubicActiveNeighbors
  exact Finset.mem_biUnion.mpr ⟨fullP, hPTouching, hSourceOther⟩

/-- The actual intrinsic spatial direct-interaction neighborhood has cardinality
at most eighteen, uniformly in the periodic volume.  This is inherited from
the four-dimensional incidence bound `6` touching plaquettes times at most
`3` other links per plaquette. -/
theorem periodicHypercubicEvenSpatialSliceActiveNeighbors_card_le_eighteen
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSliceActiveNeighbors H target).card ≤ 18 := by
  classical
  let s := periodicHypercubicEvenSpatialSliceActiveNeighbors H target
  let emb := periodicHypercubicEvenSpatialSliceLinkEmbedding H
  let fullTarget := emb target
  let fullNeighbors :=
    periodicHypercubicActiveNeighbors
      (PeriodicHypercubicEvenSideLength H) fullTarget
  have hCardImage : (s.image emb).card = s.card :=
    Finset.card_image_of_injective s
      (periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H)
  have hSubset : s.image emb ⊆ fullNeighbors := by
    simpa [s, emb, fullTarget, fullNeighbors] using
      periodicHypercubicEvenSpatialSliceActiveNeighbors_embedding_subset H target
  have hImageCard : (s.image emb).card ≤ fullNeighbors.card :=
    Finset.card_le_card hSubset
  have hFull : fullNeighbors.card ≤ 18 := by
    simpa [fullNeighbors, fullTarget, emb] using
      periodicHypercubicActiveNeighbors_card_le_eighteen
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
  rw [← hCardImage]
  exact hImageCard.trans hFull

end

end MathlibAnalytic
end MGAP4D