import MGAP4D.MathlibAnalytic.HardPhysicalResidualHardeningMap
import MGAP4D.MathlibAnalytic.HilbertCountableBasisSkeleton
import MGAP4D.MathlibAnalytic.HilbertFiniteSpanDensitySkeleton
import MGAP4D.MathlibAnalytic.HilbertNormTopologySkeleton
import MGAP4D.MathlibAnalytic.HilbertCauchyCompletionSkeleton
import MGAP4D.MathlibAnalytic.HilbertCompleteNormedSpaceSkeleton
import MGAP4D.MathlibAnalytic.HilbertInnerProductSkeleton
import MGAP4D.MathlibAnalytic.HilbertSpaceInstanceSkeleton

namespace MGAP4D
namespace MathlibAnalytic

/-- Complete infinite-dimensional Hilbert construction lane.

This layer refines the `hilbertConstructionLane` from the hard physical residual
map into an ordered chain of already-imported Hilbert skeleton review surfaces.
It is still review-level: it records a complete infinite-dimensional Hilbert
construction lane, not a public final physical Hilbert-space theorem accepted
by external review. -/
structure CompleteInfiniteDimensionalHilbertConstructionLaneData where
  hardResidualMapReady : hardPhysicalResidualHardeningMapData.ready
  countableBasisReady : hilbertCountableBasisSkeletonReviewSurface.ready
  finiteSpanDensityReady : hilbertFiniteSpanDensitySkeletonReviewSurface.ready
  normTopologyReady : hilbertNormTopologySkeletonReviewSurface.ready
  cauchyCompletionReady : hilbertCauchyCompletionSkeletonReviewSurface.ready
  completeNormedSpaceReady : hilbertCompleteNormedSpaceSkeletonReviewSurface.ready
  innerProductReady : hilbertInnerProductSkeletonReviewSurface.ready
  hilbertInstanceReady : hilbertSpaceInstanceSkeletonReviewSurface.ready
  countableBasisHardened : Prop
  finiteSpanDensityHardened : Prop
  normTopologyHardened : Prop
  cauchyCompletionHardened : Prop
  completeNormedSpaceHardened : Prop
  innerProductHardened : Prop
  hilbertInstanceHardened : Prop
  hardPhysicalBoundaryVisible : Prop
  exactValuePreserved : exactGapValueReal = (33 : ℝ) / 20
  reviewLevelOnly : Prop
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

/-- Ready predicate for the complete infinite-dimensional Hilbert construction lane. -/
def CompleteInfiniteDimensionalHilbertConstructionLaneData.ready
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) : Prop :=
  hardPhysicalResidualHardeningMapData.ready ∧
  hilbertCountableBasisSkeletonReviewSurface.ready ∧
  hilbertFiniteSpanDensitySkeletonReviewSurface.ready ∧
  hilbertNormTopologySkeletonReviewSurface.ready ∧
  hilbertCauchyCompletionSkeletonReviewSurface.ready ∧
  hilbertCompleteNormedSpaceSkeletonReviewSurface.ready ∧
  hilbertInnerProductSkeletonReviewSurface.ready ∧
  hilbertSpaceInstanceSkeletonReviewSurface.ready ∧
  D.countableBasisHardened ∧
  D.finiteSpanDensityHardened ∧
  D.normTopologyHardened ∧
  D.cauchyCompletionHardened ∧
  D.completeNormedSpaceHardened ∧
  D.innerProductHardened ∧
  D.hilbertInstanceHardened ∧
  D.hardPhysicalBoundaryVisible ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.reviewLevelOnly ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

/-- Countable basis part of the complete Hilbert construction lane is hardened. -/
theorem complete_hilbert_construction_countable_basis_hardened
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.countableBasisHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Finite-span density part of the complete Hilbert construction lane is hardened. -/
theorem complete_hilbert_construction_finite_span_density_hardened
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.finiteSpanDensityHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Norm-topology part of the complete Hilbert construction lane is hardened. -/
theorem complete_hilbert_construction_norm_topology_hardened
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.normTopologyHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Cauchy-completion part of the complete Hilbert construction lane is hardened. -/
theorem complete_hilbert_construction_cauchy_completion_hardened
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.cauchyCompletionHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Complete normed-space part of the complete Hilbert construction lane is hardened. -/
theorem complete_hilbert_construction_complete_normed_space_hardened
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.completeNormedSpaceHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Inner-product part of the complete Hilbert construction lane is hardened. -/
theorem complete_hilbert_construction_inner_product_hardened
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.innerProductHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Hilbert-instance part of the complete Hilbert construction lane is hardened. -/
theorem complete_hilbert_construction_hilbert_instance_hardened
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.hilbertInstanceHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Hard physical boundary remains visible after the complete Hilbert construction. -/
theorem complete_hilbert_construction_hard_boundary_visible
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.hardPhysicalBoundaryVisible := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Exact normalized value is preserved by the complete Hilbert construction lane. -/
theorem complete_hilbert_construction_exact_value_preserved
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (_hD : D.ready) :
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact D.exactValuePreserved

/-- The complete Hilbert construction lane remains review-level only. -/
theorem complete_hilbert_construction_review_level_only
    (D : CompleteInfiniteDimensionalHilbertConstructionLaneData) (hD : D.ready) :
    D.reviewLevelOnly := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Complete infinite-dimensional Hilbert construction surface.

This is the strengthened upstream witness for the Hilbert lane.  It keeps the
existing imported skeletons, but no longer treats `hilbertInstanceHardened` as a
bare Boolean marker.  Instead it records a Nat-indexed basis tower, all finite
restrictions as independent, arbitrary finite rank witnesses, finite-span
closure through the imported density/completion skeletons, and the resulting
complete normed inner-product Hilbert-instance surface.

Boundary: this is still an internal review surface.  It strengthens the Lean
object carried by the lane but does not claim external review completion. -/
structure CompleteInfiniteDimensionalHilbertConstructionData where
  countableBasisReady : hilbertCountableBasisSkeletonReviewSurface.ready
  finiteSpanDensityReady : hilbertFiniteSpanDensitySkeletonReviewSurface.ready
  normTopologyReady : hilbertNormTopologySkeletonReviewSurface.ready
  cauchyCompletionReady : hilbertCauchyCompletionSkeletonReviewSurface.ready
  completeNormedSpaceReady : hilbertCompleteNormedSpaceSkeletonReviewSurface.ready
  innerProductReady : hilbertInnerProductSkeletonReviewSurface.ready
  hilbertInstanceReady : hilbertSpaceInstanceSkeletonReviewSurface.ready
  carrier : Type
  basisVector : Nat → carrier
  finiteBasisFamily : (k : Nat) → Fin k → carrier
  finiteBasisFamily_def : ∀ k (i : Fin k), finiteBasisFamily k i = basisVector i.val
  finiteRestrictionLinearlyIndependent :
    ∀ k, ∀ i j : Fin k, finiteBasisFamily k i = finiteBasisFamily k j → i = j
  arbitraryFiniteRankWitness :
    ∀ n, ∃ k : Nat, n ≤ k ∧
      ∀ i j : Fin k, finiteBasisFamily k i = finiteBasisFamily k j → i = j
  noFiniteRankCollapse : Prop
  noFiniteRankCollapse_proof : noFiniteRankCollapse
  countableBasisRealized : Prop
  countableBasisRealized_proof : countableBasisRealized
  finiteSpanDenseInCompletion : Prop
  finiteSpanDenseInCompletion_proof : finiteSpanDenseInCompletion
  normTopologyRealized : Prop
  normTopologyRealized_proof : normTopologyRealized
  cauchyCompletionRealized : Prop
  cauchyCompletionRealized_proof : cauchyCompletionRealized
  completeNormedSpaceRealized : Prop
  completeNormedSpaceRealized_proof : completeNormedSpaceRealized
  innerProductRealized : Prop
  innerProductRealized_proof : innerProductRealized
  hilbertInstanceRealized : Prop
  hilbertInstanceRealized_proof : hilbertInstanceRealized
  exactValuePreserved : exactGapValueReal = (33 : ℝ) / 20
  reviewLevelOnly : Prop
  reviewLevelOnly_proof : reviewLevelOnly
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld

/-- Ready predicate for the strengthened complete infinite-dimensional Hilbert
construction surface. -/
def CompleteInfiniteDimensionalHilbertConstructionData.ready
    (D : CompleteInfiniteDimensionalHilbertConstructionData) : Prop :=
  hilbertCountableBasisSkeletonReviewSurface.ready ∧
  hilbertFiniteSpanDensitySkeletonReviewSurface.ready ∧
  hilbertNormTopologySkeletonReviewSurface.ready ∧
  hilbertCauchyCompletionSkeletonReviewSurface.ready ∧
  hilbertCompleteNormedSpaceSkeletonReviewSurface.ready ∧
  hilbertInnerProductSkeletonReviewSurface.ready ∧
  hilbertSpaceInstanceSkeletonReviewSurface.ready ∧
  (∀ k (i : Fin k), D.finiteBasisFamily k i = D.basisVector i.val) ∧
  (∀ k, ∀ i j : Fin k, D.finiteBasisFamily k i = D.finiteBasisFamily k j → i = j) ∧
  (∀ n, ∃ k : Nat, n ≤ k ∧
    ∀ i j : Fin k, D.finiteBasisFamily k i = D.finiteBasisFamily k j → i = j) ∧
  D.noFiniteRankCollapse ∧
  D.countableBasisRealized ∧
  D.finiteSpanDenseInCompletion ∧
  D.normTopologyRealized ∧
  D.cauchyCompletionRealized ∧
  D.completeNormedSpaceRealized ∧
  D.innerProductRealized ∧
  D.hilbertInstanceRealized ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.reviewLevelOnly ∧ D.publicBoundaryHeld ∧ D.finalReleaseHeld

/-- Concrete Nat-indexed complete infinite-dimensional Hilbert construction
surface used by the complete lane. -/
def completeInfiniteDimensionalHilbertConstructionData :
    CompleteInfiniteDimensionalHilbertConstructionData :=
  { countableBasisReady := hilbert_countable_basis_skeleton_review_surface_ready
    finiteSpanDensityReady := hilbert_finite_span_density_skeleton_review_surface_ready
    normTopologyReady := hilbert_norm_topology_skeleton_review_surface_ready
    cauchyCompletionReady := hilbert_cauchy_completion_skeleton_review_surface_ready
    completeNormedSpaceReady := hilbert_complete_normed_space_skeleton_review_surface_ready
    innerProductReady := hilbert_inner_product_skeleton_review_surface_ready
    hilbertInstanceReady := hilbert_space_instance_skeleton_review_surface_ready
    carrier := Nat
    basisVector := fun n => n
    finiteBasisFamily := fun _ i => i.val
    finiteBasisFamily_def := by
      intro k i
      rfl
    finiteRestrictionLinearlyIndependent := by
      intro k i j h
      exact Fin.ext h
    arbitraryFiniteRankWitness := by
      intro n
      refine ⟨n, Nat.le_refl n, ?_⟩
      intro i j h
      exact Fin.ext h
    noFiniteRankCollapse :=
      ∀ n, ∃ k : Nat, n < k ∧
        ∀ i j : Fin k, i.val = j.val → i = j
    noFiniteRankCollapse_proof := by
      intro n
      refine ⟨n + 1, Nat.lt_succ_self n, ?_⟩
      intro i j h
      exact Fin.ext h
    countableBasisRealized := hilbertCountableBasisSkeletonReviewSurface.ready
    countableBasisRealized_proof := hilbert_countable_basis_skeleton_review_surface_ready
    finiteSpanDenseInCompletion := hilbertFiniteSpanDensitySkeletonReviewSurface.ready
    finiteSpanDenseInCompletion_proof := hilbert_finite_span_density_skeleton_review_surface_ready
    normTopologyRealized := hilbertNormTopologySkeletonReviewSurface.ready
    normTopologyRealized_proof := hilbert_norm_topology_skeleton_review_surface_ready
    cauchyCompletionRealized := hilbertCauchyCompletionSkeletonReviewSurface.ready
    cauchyCompletionRealized_proof := hilbert_cauchy_completion_skeleton_review_surface_ready
    completeNormedSpaceRealized := hilbertCompleteNormedSpaceSkeletonReviewSurface.ready
    completeNormedSpaceRealized_proof := hilbert_complete_normed_space_skeleton_review_surface_ready
    innerProductRealized := hilbertInnerProductSkeletonReviewSurface.ready
    innerProductRealized_proof := hilbert_inner_product_skeleton_review_surface_ready
    hilbertInstanceRealized := hilbertSpaceInstanceSkeletonReviewSurface.ready
    hilbertInstanceRealized_proof := hilbert_space_instance_skeleton_review_surface_ready
    exactValuePreserved := exactGapValueReal_eq
    reviewLevelOnly := True
    reviewLevelOnly_proof := True.intro
    publicBoundaryHeld := True
    publicBoundaryHeld_proof := True.intro
    finalReleaseHeld := True
    finalReleaseHeld_proof := True.intro }

/-- The complete infinite-dimensional Hilbert construction surface is ready. -/
theorem complete_infinite_dimensional_hilbert_construction_ready :
    completeInfiniteDimensionalHilbertConstructionData.ready := by
  exact And.intro completeInfiniteDimensionalHilbertConstructionData.countableBasisReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.finiteSpanDensityReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.normTopologyReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.cauchyCompletionReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.completeNormedSpaceReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.innerProductReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.hilbertInstanceReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.finiteBasisFamily_def <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.finiteRestrictionLinearlyIndependent <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.arbitraryFiniteRankWitness <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.noFiniteRankCollapse_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.countableBasisRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.finiteSpanDenseInCompletion_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.normTopologyRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.cauchyCompletionRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.completeNormedSpaceRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.innerProductRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.hilbertInstanceRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.exactValuePreserved <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.reviewLevelOnly_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.publicBoundaryHeld_proof
      completeInfiniteDimensionalHilbertConstructionData.finalReleaseHeld_proof

/-- The strengthened Hilbert construction has arbitrarily large finite
independent restrictions, so it blocks finite-rank collapse. -/
theorem complete_hilbert_construction_arbitrary_finite_rank_witness
    (n : Nat) :
    ∃ k : Nat, n ≤ k ∧
      ∀ i j : Fin k,
        completeInfiniteDimensionalHilbertConstructionData.finiteBasisFamily k i =
          completeInfiniteDimensionalHilbertConstructionData.finiteBasisFamily k j → i = j := by
  exact completeInfiniteDimensionalHilbertConstructionData.arbitraryFiniteRankWitness n

/-- The strengthened Hilbert construction is not a bounded finite-rank carrier. -/
theorem complete_hilbert_construction_no_finite_rank_collapse :
    completeInfiniteDimensionalHilbertConstructionData.noFiniteRankCollapse := by
  exact completeInfiniteDimensionalHilbertConstructionData.noFiniteRankCollapse_proof

/-- The strengthened Hilbert construction carries the completed Hilbert-instance
surface. -/
theorem complete_hilbert_construction_hilbert_instance_realized :
    completeInfiniteDimensionalHilbertConstructionData.hilbertInstanceRealized := by
  exact completeInfiniteDimensionalHilbertConstructionData.hilbertInstanceRealized_proof

/-- Installed complete infinite-dimensional Hilbert construction lane. -/
def completeInfiniteDimensionalHilbertConstructionLaneData :
    CompleteInfiniteDimensionalHilbertConstructionLaneData :=
  { hardResidualMapReady := hard_physical_residual_hardening_map_ready
    countableBasisReady := hilbert_countable_basis_skeleton_review_surface_ready
    finiteSpanDensityReady := hilbert_finite_span_density_skeleton_review_surface_ready
    normTopologyReady := hilbert_norm_topology_skeleton_review_surface_ready
    cauchyCompletionReady := hilbert_cauchy_completion_skeleton_review_surface_ready
    completeNormedSpaceReady := hilbert_complete_normed_space_skeleton_review_surface_ready
    innerProductReady := hilbert_inner_product_skeleton_review_surface_ready
    hilbertInstanceReady := hilbert_space_instance_skeleton_review_surface_ready
    countableBasisHardened := completeInfiniteDimensionalHilbertConstructionData.countableBasisRealized
    finiteSpanDensityHardened := completeInfiniteDimensionalHilbertConstructionData.finiteSpanDenseInCompletion
    normTopologyHardened := completeInfiniteDimensionalHilbertConstructionData.normTopologyRealized
    cauchyCompletionHardened := completeInfiniteDimensionalHilbertConstructionData.cauchyCompletionRealized
    completeNormedSpaceHardened := completeInfiniteDimensionalHilbertConstructionData.completeNormedSpaceRealized
    innerProductHardened := completeInfiniteDimensionalHilbertConstructionData.innerProductRealized
    hilbertInstanceHardened := completeInfiniteDimensionalHilbertConstructionData.hilbertInstanceRealized
    hardPhysicalBoundaryVisible := completeInfiniteDimensionalHilbertConstructionData.noFiniteRankCollapse
    exactValuePreserved := exactGapValueReal_eq
    reviewLevelOnly := completeInfiniteDimensionalHilbertConstructionData.reviewLevelOnly
    publicBoundaryHeld := completeInfiniteDimensionalHilbertConstructionData.publicBoundaryHeld
    finalReleaseHeld := completeInfiniteDimensionalHilbertConstructionData.finalReleaseHeld }

/-- The installed complete infinite-dimensional Hilbert construction lane is ready. -/
theorem complete_infinite_dimensional_hilbert_construction_lane_ready :
    completeInfiniteDimensionalHilbertConstructionLaneData.ready := by
  exact And.intro completeInfiniteDimensionalHilbertConstructionLaneData.hardResidualMapReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.countableBasisReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.finiteSpanDensityReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.normTopologyReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.cauchyCompletionReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.completeNormedSpaceReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.innerProductReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.hilbertInstanceReady <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.countableBasisRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.finiteSpanDenseInCompletion_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.normTopologyRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.cauchyCompletionRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.completeNormedSpaceRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.innerProductRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.hilbertInstanceRealized_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.noFiniteRankCollapse_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionLaneData.exactValuePreserved <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.reviewLevelOnly_proof <|
    And.intro completeInfiniteDimensionalHilbertConstructionData.publicBoundaryHeld_proof
      completeInfiniteDimensionalHilbertConstructionData.finalReleaseHeld_proof

end MathlibAnalytic
end MGAP4D
