import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheoremDirect

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- R2-to-R3 promotion surface.

R2 supplies the coordinate/closure mechanics: square-distance bounds, coordinate
Lipschitz estimates, coordinate continuity, relation-set closedness, and the
direct closed-graph witness.  R3 begins when that witness is promoted to the
closed graph theorem for the original diagonal operator graph. -/
def concreteL2R2ToR3ClosedGraphPromotion : Prop :=
  concreteAnalyticSpineL2R2CoordinateSquareDistanceBoundsReady ∧
  concreteL2R2DirectClosedGraphWitness ∧
  concreteL2R2OriginalDiagonalOperatorClosedTheoremDirect

/-- The R2-to-R3 closed graph promotion is proved. -/
theorem concrete_l2_r2_to_r3_closed_graph_promotion_ready :
    concreteL2R2ToR3ClosedGraphPromotion := by
  exact ⟨
    concrete_analytic_spine_l2_r2_coordinate_square_distance_bounds_ready,
    concrete_l2_r2_direct_closed_graph_witness,
    concrete_l2_r2_original_diagonal_operator_closed_theorem_direct⟩

/-- R3 closed graph promotion packet.

This is the correct semantic home for the direct original diagonal graph
closedness theorem.  It retains the older `L2R2` theorem names as historical
construction names, but classifies the achieved theorem as R3-level closed graph
promotion. -/
def concreteL2R3ClosedGraphPromotionPacket : Prop :=
  concreteL2R2ToR3ClosedGraphPromotion ∧
  concreteL2R2ClosedOperatorDirectPromotionPacket

/-- The R3 closed graph promotion packet is ready. -/
theorem concrete_l2_r3_closed_graph_promotion_packet_ready :
    concreteL2R3ClosedGraphPromotionPacket := by
  exact ⟨
    concrete_l2_r2_to_r3_closed_graph_promotion_ready,
    concrete_l2_r2_closed_operator_direct_promotion_packet_ready⟩

/-- R3 boundary: closed graph has been promoted, but this is not yet a
self-adjointness theorem, spectral theorem, PVM construction, or positive
spectral-weight theorem. -/
def concreteL2R3ClosedGraphPromotionBoundary : Prop :=
  concreteL2R2OriginalDiagonalOperatorClosedTheoremDirect ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSpectralTheorem ∧
  concreteL2R2ClosedOperatorBoundaryNotPVM ∧
  concreteL2R2ClosedOperatorBoundaryNotPositiveSpectralWeight

/-- The R3 closed graph promotion boundary is ready. -/
theorem concrete_l2_r3_closed_graph_promotion_boundary_ready :
    concreteL2R3ClosedGraphPromotionBoundary := by
  exact ⟨
    concrete_l2_r2_original_diagonal_operator_closed_theorem_direct,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_spectral_theorem,
    concrete_l2_r2_closed_operator_boundary_not_pvm,
    concrete_l2_r2_closed_operator_boundary_not_positive_spectral_weight⟩

/-- Public R3 readiness surface for the closed graph promotion. -/
def concreteAnalyticSpineL2R3ClosedGraphPromotionReady : Prop :=
  concreteL2R3ClosedGraphPromotionPacket ∧
  concreteL2R3ClosedGraphPromotionBoundary

/-- The public R3 readiness surface for the closed graph promotion is ready. -/
theorem concrete_analytic_spine_l2_r3_closed_graph_promotion_ready :
    concreteAnalyticSpineL2R3ClosedGraphPromotionReady := by
  exact ⟨
    concrete_l2_r3_closed_graph_promotion_packet_ready,
    concrete_l2_r3_closed_graph_promotion_boundary_ready⟩

end

end MathlibAnalytic
end MGAP4D
