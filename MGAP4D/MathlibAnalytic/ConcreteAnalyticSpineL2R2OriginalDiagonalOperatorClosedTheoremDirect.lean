import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateSquareDistanceBounds
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheorem
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Direct, non-conditional closedness theorem for the original R2 diagonal graph.

This is the promotion point where the previously conditional closedness theorem is
no longer routed through `DiagonalGraphEqualsClosureGeneratedGraph`.  The proof
uses the coordinate-square-distance route:

`coordinate square bounds → coordinate Lipschitz → coordinate continuity →
coordinate relation sets closed → pointwise relation set closed → direct closed
witness → original diagonal graph closed`.
-/
def concreteL2R2OriginalDiagonalOperatorClosedTheoremDirect : Prop :=
  concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The direct original diagonal operator closed theorem is proved. -/
theorem concrete_l2_r2_original_diagonal_operator_closed_theorem_direct :
    concreteL2R2OriginalDiagonalOperatorClosedTheoremDirect := by
  unfold concreteL2R2OriginalDiagonalOperatorClosedTheoremDirect
  exact concrete_l2_r2_original_diagonal_graph_closed

/-- The direct theorem and the older conditional theorem agree on the same
closedness target. -/
def concreteL2R2OriginalDiagonalOperatorClosedTheoremDirectRefinesConditional : Prop :=
  concreteL2R2OriginalDiagonalOperatorClosedTheoremDirect ∧
  concreteL2R2OriginalDiagonalOperatorClosedTheoremConditional

/-- The direct theorem refines the conditional closedness surface without removing
that older surface. -/
theorem concrete_l2_r2_original_diagonal_operator_closed_theorem_direct_refines_conditional :
    concreteL2R2OriginalDiagonalOperatorClosedTheoremDirectRefinesConditional := by
  exact ⟨
    concrete_l2_r2_original_diagonal_operator_closed_theorem_direct,
    concrete_l2_r2_original_diagonal_operator_closed_theorem_conditional⟩

/-- Closed-operator promotion packet after the direct graph-closedness theorem.

This is still deliberately below self-adjointness, spectral theorem, PVM, exact
atom, and positive spectral weight.  It promotes only the original R2 diagonal
graph closedness theorem. -/
def concreteL2R2ClosedOperatorDirectPromotionPacket : Prop :=
  concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady ∧
  concreteAnalyticSpineL2R2CoordinateSquareDistanceBoundsReady ∧
  concreteL2R2OriginalDiagonalOperatorClosedTheoremDirect ∧
  concreteL2R2OriginalDiagonalOperatorClosedTheoremDirectRefinesConditional ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSpectralTheorem ∧
  concreteL2R2ClosedOperatorBoundaryNotPVM ∧
  concreteL2R2ClosedOperatorBoundaryNotPositiveSpectralWeight

/-- The closed-operator direct promotion packet is ready. -/
theorem concrete_l2_r2_closed_operator_direct_promotion_packet_ready :
    concreteL2R2ClosedOperatorDirectPromotionPacket := by
  exact ⟨
    concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready,
    concrete_analytic_spine_l2_r2_coordinate_square_distance_bounds_ready,
    concrete_l2_r2_original_diagonal_operator_closed_theorem_direct,
    concrete_l2_r2_original_diagonal_operator_closed_theorem_direct_refines_conditional,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_spectral_theorem,
    concrete_l2_r2_closed_operator_boundary_not_pvm,
    concrete_l2_r2_closed_operator_boundary_not_positive_spectral_weight⟩

/-- Public readiness surface for the direct original diagonal closed-operator
promotion. -/
def concreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheoremDirectReady : Prop :=
  concreteL2R2ClosedOperatorDirectPromotionPacket

/-- The public readiness surface for the direct original diagonal closed-operator
promotion is ready. -/
theorem concrete_analytic_spine_l2_r2_original_diagonal_operator_closed_theorem_direct_ready :
    concreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheoremDirectReady := by
  exact concrete_l2_r2_closed_operator_direct_promotion_packet_ready

end

end MathlibAnalytic
end MGAP4D
