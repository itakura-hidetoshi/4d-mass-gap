import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DirectClosedGraphWitness

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- Coordinate-limit obligation promotes to the direct closed-graph witness.

Once every point in the graph-norm closure satisfies the pointwise diagonal
relation, the already-proved reconstruction theorem puts it back in the original
diagonal graph. -/
theorem concrete_l2_r2_direct_closed_graph_witness_of_coordinate_limit
    (hcoord : concreteL2R2ClosureMembershipToCoordinateLimitObligation) :
    concreteL2R2DirectClosedGraphWitness := by
  intro p hp
  exact concrete_l2_r2_diagonal_graph_mem_of_pointwise_relation (hcoord hp)

/-- Coordinate-limit obligation promotes all the way to original diagonal graph
closedness. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_coordinate_limit
    (hcoord : concreteL2R2ClosureMembershipToCoordinateLimitObligation) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  exact concrete_l2_r2_original_diagonal_graph_closed_of_direct_witness
    (concrete_l2_r2_direct_closed_graph_witness_of_coordinate_limit hcoord)

/-- Promotion proposition from coordinate-limit obligation to direct witness. -/
def concreteL2R2CoordinateLimitToDirectWitnessPromotion : Prop :=
  concreteL2R2ClosureMembershipToCoordinateLimitObligation →
    concreteL2R2DirectClosedGraphWitness

/-- The coordinate-limit-to-direct-witness promotion is proved. -/
theorem concrete_l2_r2_coordinate_limit_to_direct_witness_promotion_ready :
    concreteL2R2CoordinateLimitToDirectWitnessPromotion := by
  intro hcoord
  exact concrete_l2_r2_direct_closed_graph_witness_of_coordinate_limit hcoord

/-- Promotion proposition from coordinate-limit obligation to original graph
closedness. -/
def concreteL2R2CoordinateLimitToOriginalGraphClosedPromotion : Prop :=
  concreteL2R2ClosureMembershipToCoordinateLimitObligation →
    concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The coordinate-limit-to-original-graph-closed promotion is proved. -/
theorem concrete_l2_r2_coordinate_limit_to_original_graph_closed_promotion_ready :
    concreteL2R2CoordinateLimitToOriginalGraphClosedPromotion := by
  intro hcoord
  exact concrete_l2_r2_original_diagonal_graph_closed_of_coordinate_limit hcoord

/-- Readiness predicate for the coordinate-limit bridge layer. -/
def concreteAnalyticSpineL2R2DirectClosedGraphCoordinateLimitBridgeReady : Prop :=
  concreteL2R2CoordinateLimitToDirectWitnessPromotion ∧
  concreteL2R2CoordinateLimitToOriginalGraphClosedPromotion ∧
  concreteAnalyticSpineL2R2DirectClosedGraphWitnessSurfaceReady

/-- The coordinate-limit bridge layer is ready. -/
theorem concrete_analytic_spine_l2_r2_direct_closed_graph_coordinate_limit_bridge_ready :
    concreteAnalyticSpineL2R2DirectClosedGraphCoordinateLimitBridgeReady := by
  exact ⟨
    concrete_l2_r2_coordinate_limit_to_direct_witness_promotion_ready,
    concrete_l2_r2_coordinate_limit_to_original_graph_closed_promotion_ready,
    concrete_analytic_spine_l2_r2_direct_closed_graph_witness_surface_ready⟩

end

end MathlibAnalytic
end MGAP4D
