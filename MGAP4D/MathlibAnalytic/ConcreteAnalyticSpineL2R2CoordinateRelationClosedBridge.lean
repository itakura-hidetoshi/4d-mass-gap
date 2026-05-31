import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2PointwiseRelationIInterBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- Continuity obligation for the second-coordinate evaluation of a graph pair at
coordinate `n`, with respect to the explicit graph-norm topology. -/
def concreteL2R2GraphPairSndCoordinateContinuous (n : ℕ) : Prop :=
  @Continuous ConcreteL2GraphPairSpace ℝ concreteL2GraphNormTopology _
    (fun p : ConcreteL2GraphPairSpace => p.2.1 n)

/-- Continuity obligation for the weighted first-coordinate evaluation of a graph
pair at coordinate `n`, with respect to the explicit graph-norm topology. -/
def concreteL2R2GraphPairWeightedFstCoordinateContinuous (n : ℕ) : Prop :=
  @Continuous ConcreteL2GraphPairSpace ℝ concreteL2GraphNormTopology _
    (fun p : ConcreteL2GraphPairSpace => concreteL2DiagonalWeight n * p.1.1 n)

/-- If the two coordinate functions defining the `n`-th diagonal relation are
continuous, then the `n`-th coordinate relation set is closed.

This is the Mathlib `isClosed_eq` step: the relation set is the equalizer of the
continuous maps `p ↦ p.2 n` and `p ↦ w_n * p.1 n`. -/
theorem concrete_l2_r2_coordinate_relation_set_closed_of_coordinate_continuity
    (n : ℕ)
    (hsnd : concreteL2R2GraphPairSndCoordinateContinuous n)
    (hfst : concreteL2R2GraphPairWeightedFstCoordinateContinuous n) :
    concreteL2R2CoordinateRelationSetClosed n := by
  unfold concreteL2R2CoordinateRelationSetClosed
  unfold concreteL2R2GraphPairSndCoordinateContinuous at hsnd
  unfold concreteL2R2GraphPairWeightedFstCoordinateContinuous at hfst
  letI : TopologicalSpace ConcreteL2GraphPairSpace := concreteL2GraphNormTopology
  change IsClosed
    {p : ConcreteL2GraphPairSpace |
      p.2.1 n = concreteL2DiagonalWeight n * p.1.1 n}
  exact isClosed_eq hsnd hfst

/-- Coordinate-continuity package for all coordinate relation sets. -/
def concreteL2R2AllCoordinateRelationContinuity : Prop :=
  ∀ n : ℕ,
    concreteL2R2GraphPairSndCoordinateContinuous n ∧
      concreteL2R2GraphPairWeightedFstCoordinateContinuous n

/-- All coordinate-continuity obligations promote to all coordinate relation sets
being closed. -/
theorem concrete_l2_r2_coordinate_relation_sets_closed_of_all_coordinate_continuity
    (hcont : concreteL2R2AllCoordinateRelationContinuity) :
    ∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n := by
  intro n
  exact concrete_l2_r2_coordinate_relation_set_closed_of_coordinate_continuity n
    (hcont n).1 (hcont n).2

/-- All coordinate-continuity obligations promote to the pointwise relation set
being closed. -/
theorem concrete_l2_r2_pointwise_relation_set_closed_of_all_coordinate_continuity
    (hcont : concreteL2R2AllCoordinateRelationContinuity) :
    concreteL2R2PointwiseRelationSetClosed := by
  exact concrete_l2_r2_pointwise_relation_set_closed_of_coordinate_relation_sets_closed
    (concrete_l2_r2_coordinate_relation_sets_closed_of_all_coordinate_continuity hcont)

/-- All coordinate-continuity obligations promote to the coordinate-limit
obligation. -/
theorem concrete_l2_r2_closure_membership_to_coordinate_limit_of_all_coordinate_continuity
    (hcont : concreteL2R2AllCoordinateRelationContinuity) :
    concreteL2R2ClosureMembershipToCoordinateLimitObligation := by
  exact concrete_l2_r2_closure_membership_to_coordinate_limit_of_relation_set_closed
    (concrete_l2_r2_pointwise_relation_set_closed_of_all_coordinate_continuity hcont)

/-- All coordinate-continuity obligations promote to the direct closed-graph
witness. -/
theorem concrete_l2_r2_direct_closed_graph_witness_of_all_coordinate_continuity
    (hcont : concreteL2R2AllCoordinateRelationContinuity) :
    concreteL2R2DirectClosedGraphWitness := by
  exact concrete_l2_r2_direct_closed_graph_witness_of_coordinate_limit
    (concrete_l2_r2_closure_membership_to_coordinate_limit_of_all_coordinate_continuity hcont)

/-- All coordinate-continuity obligations promote to original diagonal graph
closedness. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_all_coordinate_continuity
    (hcont : concreteL2R2AllCoordinateRelationContinuity) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  exact concrete_l2_r2_original_diagonal_graph_closed_of_coordinate_limit
    (concrete_l2_r2_closure_membership_to_coordinate_limit_of_all_coordinate_continuity hcont)

/-- Promotion proposition from all coordinate-continuity obligations to closedness
of all coordinate relation sets. -/
def concreteL2R2AllCoordinateContinuityToCoordinateRelationClosedPromotion : Prop :=
  concreteL2R2AllCoordinateRelationContinuity →
    ∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n

/-- The all-coordinate-continuity to coordinate-relation-closedness promotion is
proved. -/
theorem concrete_l2_r2_all_coordinate_continuity_to_coordinate_relation_closed_promotion_ready :
    concreteL2R2AllCoordinateContinuityToCoordinateRelationClosedPromotion := by
  intro hcont
  exact concrete_l2_r2_coordinate_relation_sets_closed_of_all_coordinate_continuity hcont

/-- Promotion proposition from all coordinate-continuity obligations to original
diagonal graph closedness. -/
def concreteL2R2AllCoordinateContinuityToOriginalGraphClosedPromotion : Prop :=
  concreteL2R2AllCoordinateRelationContinuity →
    concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The all-coordinate-continuity to original-graph-closedness promotion is
proved. -/
theorem concrete_l2_r2_all_coordinate_continuity_to_original_graph_closed_promotion_ready :
    concreteL2R2AllCoordinateContinuityToOriginalGraphClosedPromotion := by
  intro hcont
  exact concrete_l2_r2_original_diagonal_graph_closed_of_all_coordinate_continuity hcont

/-- Readiness predicate for the coordinate-relation closedness bridge. -/
def concreteAnalyticSpineL2R2CoordinateRelationClosedBridgeReady : Prop :=
  concreteAnalyticSpineL2R2PointwiseRelationIInterBridgeReady ∧
  concreteL2R2AllCoordinateContinuityToCoordinateRelationClosedPromotion ∧
  concreteL2R2AllCoordinateContinuityToOriginalGraphClosedPromotion

/-- The coordinate-relation closedness bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_coordinate_relation_closed_bridge_ready :
    concreteAnalyticSpineL2R2CoordinateRelationClosedBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_pointwise_relation_iInter_bridge_ready,
    concrete_l2_r2_all_coordinate_continuity_to_coordinate_relation_closed_promotion_ready,
    concrete_l2_r2_all_coordinate_continuity_to_original_graph_closed_promotion_ready⟩

end

end MathlibAnalytic
end MGAP4D
