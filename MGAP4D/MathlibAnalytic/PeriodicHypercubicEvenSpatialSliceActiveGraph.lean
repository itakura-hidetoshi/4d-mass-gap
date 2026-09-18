import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveNeighborBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicL1SpatialCovariance
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance spatialSliceActiveGraphSideLengthNeZero
    (H : Nat) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

local instance spatialSliceActiveGraphLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Sharing one intrinsic spatial plaquette is symmetric in the two links. -/
theorem periodicHypercubicEvenSpatialSliceLinksSharePlaquette_comm
    (H : Nat)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source ↔
      periodicHypercubicEvenSpatialSliceLinksSharePlaquette H source target := by
  constructor
  · rintro ⟨p, hTarget, hSource⟩
    exact ⟨p, hSource, hTarget⟩
  · rintro ⟨p, hSource, hTarget⟩
    exact ⟨p, hTarget, hSource⟩

/-- The intrinsic spatial-link interaction graph. Distinct spatial links are
adjacent exactly when they occur in one common intrinsic Wilson plaquette. -/
def periodicHypercubicEvenSpatialSliceActiveGraph
    (H : Nat) :
    SimpleGraph (PeriodicHypercubicEvenSpatialSliceLink H) :=
  { Adj := fun target source =>
      source ≠ target ∧
        periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source
    symm := by
      intro target source h
      refine ⟨Ne.symm h.1, ?_⟩
      exact
        (periodicHypercubicEvenSpatialSliceLinksSharePlaquette_comm
          H target source).mp h.2
    loopless := { irrefl := fun target h => h.1 rfl } }

/-- Graph adjacency is exactly membership in the already-canonical intrinsic
active-neighbor finset. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
    (H : Nat)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target source ↔
      source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target := by
  change
    (source ≠ target ∧
      periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source) ↔
      source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target
  exact
    (periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff
      H target source).symm

/-- The canonical finite adjacency row of the spatial-link graph.  Reusing
the already-formalized active-neighbor finset avoids introducing a second
decidable presentation of the same relation. -/
noncomputable def periodicHypercubicEvenSpatialSliceActiveGraphAdjFinset
    (H : Nat)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
  periodicHypercubicEvenSpatialSliceActiveNeighbors H target

@[simp] theorem periodicHypercubicEvenSpatialSliceActiveGraph_mem_adjFinset_iff
    (H : Nat)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈ periodicHypercubicEvenSpatialSliceActiveGraphAdjFinset H target ↔
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target source := by
  rw [periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors]
  rfl

/-- Consequently every spatial-link graph adjacency row has cardinality at
most eighteen, uniformly in the periodic volume. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_adjFinset_card_le_eighteen
    (H : Nat)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSliceActiveGraphAdjFinset H target).card ≤
      18 := by
  exact periodicHypercubicEvenSpatialSliceActiveNeighbors_card_le_eighteen H target

/-- One intrinsic spatial-link graph edge embeds into the full four-dimensional
physical active-neighbor relation. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_adj_embedding_mem_activeNeighbors
    (H : Nat)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hAdj :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target source) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H source ∈
      periodicHypercubicActiveNeighbors
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  classical
  have hActive :
      source ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H target :=
    (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
      H target source).mp hAdj
  have hImage :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H source ∈
        (periodicHypercubicEvenSpatialSliceActiveNeighbors H target).image
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H) := by
    exact Finset.mem_image.mpr ⟨source, hActive, rfl⟩
  exact
    periodicHypercubicEvenSpatialSliceActiveNeighbors_embedding_subset
      H target hImage

/-- Hence one intrinsic spatial-link graph edge is one of the canonical
coordinate-neighbor moves in the full periodic edge geometry. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_adj_embedding_mem_coordinateNeighbors
    (H : Nat)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hAdj :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target source) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H source ∈
      periodicHypercubicCoordinateNeighbors
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
  exact
    periodicHypercubicActiveNeighbors_subset_coordinateNeighbors
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
      (periodicHypercubicEvenSpatialSliceActiveGraph_adj_embedding_mem_activeNeighbors
        H hAdj)

/-- Every one-step intrinsic spatial interaction changes the embedded
base-vertex periodic L1 distance by at most two. This is the local metric
bridge needed before any spatial shell/path estimate is transported to the
terminal-response radius. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_adj_baseL1Distance_le_two
    (H : Nat)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hAdj :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target source) :
    periodicHypercubicEdgeBaseL1Distance
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) ≤ 2 := by
  exact
    periodicHypercubicEdgeBaseL1Distance_le_two_of_coordinateNeighbor
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
      (periodicHypercubicEvenSpatialSliceActiveGraph_adj_embedding_mem_coordinateNeighbors
        H hAdj)

end

end MathlibAnalytic
end MGAP4D
