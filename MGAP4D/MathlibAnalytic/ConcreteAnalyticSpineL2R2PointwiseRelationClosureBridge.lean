import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalGraphCoordinateLaw
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DirectClosedGraphCoordinateLimitBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- The set of graph pairs satisfying the pointwise diagonal relation. -/
def concreteL2R2PointwiseRelationSet : Set ConcreteL2GraphPairSpace :=
  {p : ConcreteL2GraphPairSpace | concreteL2R2DiagonalGraphPointwiseRelation p}

/-- Closedness obligation for the pointwise diagonal-relation set in the
explicit graph-norm topology. -/
def concreteL2R2PointwiseRelationSetClosed : Prop :=
  @IsClosed ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    concreteL2R2PointwiseRelationSet

/-- The original diagonal graph is contained in the pointwise diagonal-relation
set. -/
theorem concrete_l2_r2_diagonal_graph_subset_pointwise_relation_set :
    ConcreteL2DiagonalGraphL2Carrier ⊆ concreteL2R2PointwiseRelationSet := by
  intro p hp
  exact concrete_l2_r2_diagonal_graph_pointwise_relation_of_mem hp

/-- If the pointwise diagonal-relation set is closed, then closure membership in
the original diagonal graph implies the pointwise coordinate relation.

This is the Mathlib `closure_minimal` step that turns the remaining analytic
limit-passage problem into a closedness theorem for the relation set. -/
theorem concrete_l2_r2_closure_membership_to_coordinate_limit_of_relation_set_closed
    (hclosed : concreteL2R2PointwiseRelationSetClosed) :
    concreteL2R2ClosureMembershipToCoordinateLimitObligation := by
  unfold concreteL2R2ClosureMembershipToCoordinateLimitObligation
  unfold concreteL2R2PointwiseRelationSetClosed at hclosed
  exact @closure_minimal ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2DiagonalGraphL2Carrier concreteL2R2PointwiseRelationSet
    concrete_l2_r2_diagonal_graph_subset_pointwise_relation_set hclosed

/-- Closed pointwise relation set promotes to the direct closed-graph witness. -/
theorem concrete_l2_r2_direct_closed_graph_witness_of_relation_set_closed
    (hclosed : concreteL2R2PointwiseRelationSetClosed) :
    concreteL2R2DirectClosedGraphWitness := by
  exact concrete_l2_r2_direct_closed_graph_witness_of_coordinate_limit
    (concrete_l2_r2_closure_membership_to_coordinate_limit_of_relation_set_closed hclosed)

/-- Closed pointwise relation set promotes to original diagonal graph closedness. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_relation_set_closed
    (hclosed : concreteL2R2PointwiseRelationSetClosed) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  exact concrete_l2_r2_original_diagonal_graph_closed_of_coordinate_limit
    (concrete_l2_r2_closure_membership_to_coordinate_limit_of_relation_set_closed hclosed)

/-- Promotion proposition from closed pointwise relation set to coordinate-limit
obligation. -/
def concreteL2R2RelationSetClosedToCoordinateLimitPromotion : Prop :=
  concreteL2R2PointwiseRelationSetClosed →
    concreteL2R2ClosureMembershipToCoordinateLimitObligation

/-- The relation-set-closed to coordinate-limit promotion is proved. -/
theorem concrete_l2_r2_relation_set_closed_to_coordinate_limit_promotion_ready :
    concreteL2R2RelationSetClosedToCoordinateLimitPromotion := by
  intro hclosed
  exact concrete_l2_r2_closure_membership_to_coordinate_limit_of_relation_set_closed hclosed

/-- Promotion proposition from closed pointwise relation set to direct witness. -/
def concreteL2R2RelationSetClosedToDirectWitnessPromotion : Prop :=
  concreteL2R2PointwiseRelationSetClosed →
    concreteL2R2DirectClosedGraphWitness

/-- The relation-set-closed to direct-witness promotion is proved. -/
theorem concrete_l2_r2_relation_set_closed_to_direct_witness_promotion_ready :
    concreteL2R2RelationSetClosedToDirectWitnessPromotion := by
  intro hclosed
  exact concrete_l2_r2_direct_closed_graph_witness_of_relation_set_closed hclosed

/-- Promotion proposition from closed pointwise relation set to original graph
closedness. -/
def concreteL2R2RelationSetClosedToOriginalGraphClosedPromotion : Prop :=
  concreteL2R2PointwiseRelationSetClosed →
    concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The relation-set-closed to original-graph-closed promotion is proved. -/
theorem concrete_l2_r2_relation_set_closed_to_original_graph_closed_promotion_ready :
    concreteL2R2RelationSetClosedToOriginalGraphClosedPromotion := by
  intro hclosed
  exact concrete_l2_r2_original_diagonal_graph_closed_of_relation_set_closed hclosed

/-- Readiness predicate for the pointwise-relation closure bridge. -/
def concreteAnalyticSpineL2R2PointwiseRelationClosureBridgeReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalGraphCoordinateLawReady ∧
  concreteAnalyticSpineL2R2DirectClosedGraphCoordinateLimitBridgeReady ∧
  concreteL2R2RelationSetClosedToCoordinateLimitPromotion ∧
  concreteL2R2RelationSetClosedToDirectWitnessPromotion ∧
  concreteL2R2RelationSetClosedToOriginalGraphClosedPromotion

/-- The pointwise-relation closure bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_pointwise_relation_closure_bridge_ready :
    concreteAnalyticSpineL2R2PointwiseRelationClosureBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_diagonal_graph_coordinate_law_ready,
    concrete_analytic_spine_l2_r2_direct_closed_graph_coordinate_limit_bridge_ready,
    concrete_l2_r2_relation_set_closed_to_coordinate_limit_promotion_ready,
    concrete_l2_r2_relation_set_closed_to_direct_witness_promotion_ready,
    concrete_l2_r2_relation_set_closed_to_original_graph_closed_promotion_ready⟩

end

end MathlibAnalytic
end MGAP4D
