import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2PointwiseRelationClosureBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- The single-coordinate diagonal relation set. -/
def concreteL2R2CoordinateRelationSet (n : ℕ) : Set ConcreteL2GraphPairSpace :=
  {p : ConcreteL2GraphPairSpace |
    p.2.1 n = concreteL2DiagonalWeight n * p.1.1 n}

/-- Closedness of the single-coordinate relation set in the graph-norm topology. -/
def concreteL2R2CoordinateRelationSetClosed (n : ℕ) : Prop :=
  @IsClosed ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    (concreteL2R2CoordinateRelationSet n)

/-- The pointwise relation set is the intersection of its single-coordinate
relation sets. -/
theorem concrete_l2_r2_pointwise_relation_set_eq_iInter_coordinate_relation_sets :
    concreteL2R2PointwiseRelationSet =
      ⋂ n : ℕ, concreteL2R2CoordinateRelationSet n := by
  ext p
  simp [concreteL2R2PointwiseRelationSet,
    concreteL2R2CoordinateRelationSet,
    concreteL2R2DiagonalGraphPointwiseRelation]

/-- If every single-coordinate relation set is closed, then the full pointwise
relation set is closed. -/
theorem concrete_l2_r2_pointwise_relation_set_closed_of_coordinate_relation_sets_closed
    (hclosed : ∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n) :
    concreteL2R2PointwiseRelationSetClosed := by
  unfold concreteL2R2PointwiseRelationSetClosed
  letI : TopologicalSpace ConcreteL2GraphPairSpace := concreteL2GraphNormTopology
  change IsClosed concreteL2R2PointwiseRelationSet
  rw [concrete_l2_r2_pointwise_relation_set_eq_iInter_coordinate_relation_sets]
  exact isClosed_iInter (fun n => by
    unfold concreteL2R2CoordinateRelationSetClosed at hclosed
    exact hclosed n)

/-- Coordinate-relation-set closedness promotes to the coordinate-limit
obligation. -/
theorem concrete_l2_r2_closure_membership_to_coordinate_limit_of_coordinate_relation_sets_closed
    (hclosed : ∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n) :
    concreteL2R2ClosureMembershipToCoordinateLimitObligation := by
  exact concrete_l2_r2_closure_membership_to_coordinate_limit_of_relation_set_closed
    (concrete_l2_r2_pointwise_relation_set_closed_of_coordinate_relation_sets_closed hclosed)

/-- Coordinate-relation-set closedness promotes to the direct closed-graph
witness. -/
theorem concrete_l2_r2_direct_closed_graph_witness_of_coordinate_relation_sets_closed
    (hclosed : ∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n) :
    concreteL2R2DirectClosedGraphWitness := by
  exact concrete_l2_r2_direct_closed_graph_witness_of_relation_set_closed
    (concrete_l2_r2_pointwise_relation_set_closed_of_coordinate_relation_sets_closed hclosed)

/-- Coordinate-relation-set closedness promotes to original diagonal graph
closedness. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_coordinate_relation_sets_closed
    (hclosed : ∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  exact concrete_l2_r2_original_diagonal_graph_closed_of_relation_set_closed
    (concrete_l2_r2_pointwise_relation_set_closed_of_coordinate_relation_sets_closed hclosed)

/-- Promotion proposition from coordinate relation closedness to pointwise relation
closedness. -/
def concreteL2R2CoordinateRelationSetsClosedToPointwiseRelationSetClosedPromotion : Prop :=
  (∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n) →
    concreteL2R2PointwiseRelationSetClosed

/-- The coordinate-relation-set closedness to pointwise-relation-set closedness
promotion is proved. -/
theorem concrete_l2_r2_coordinate_relation_sets_closed_to_pointwise_relation_set_closed_promotion_ready :
    concreteL2R2CoordinateRelationSetsClosedToPointwiseRelationSetClosedPromotion := by
  intro hclosed
  exact concrete_l2_r2_pointwise_relation_set_closed_of_coordinate_relation_sets_closed hclosed

/-- Promotion proposition from coordinate relation closedness to coordinate-limit
obligation. -/
def concreteL2R2CoordinateRelationSetsClosedToCoordinateLimitPromotion : Prop :=
  (∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n) →
    concreteL2R2ClosureMembershipToCoordinateLimitObligation

/-- The coordinate-relation-set closedness to coordinate-limit promotion is
proved. -/
theorem concrete_l2_r2_coordinate_relation_sets_closed_to_coordinate_limit_promotion_ready :
    concreteL2R2CoordinateRelationSetsClosedToCoordinateLimitPromotion := by
  intro hclosed
  exact concrete_l2_r2_closure_membership_to_coordinate_limit_of_coordinate_relation_sets_closed hclosed

/-- Readiness predicate for the `iInter` bridge. -/
def concreteAnalyticSpineL2R2PointwiseRelationIInterBridgeReady : Prop :=
  concreteAnalyticSpineL2R2PointwiseRelationClosureBridgeReady ∧
  concreteL2R2CoordinateRelationSetsClosedToPointwiseRelationSetClosedPromotion ∧
  concreteL2R2CoordinateRelationSetsClosedToCoordinateLimitPromotion

/-- The `iInter` bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_pointwise_relation_iInter_bridge_ready :
    concreteAnalyticSpineL2R2PointwiseRelationIInterBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_pointwise_relation_closure_bridge_ready,
    concrete_l2_r2_coordinate_relation_sets_closed_to_pointwise_relation_set_closed_promotion_ready,
    concrete_l2_r2_coordinate_relation_sets_closed_to_coordinate_limit_promotion_ready⟩

end

end MathlibAnalytic
end MGAP4D
