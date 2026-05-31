import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R3ToR4SelfAdjointnessPreconditionHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2AdjointContainmentSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Verified R4 pre-self-adjointness evidence packet.

This packet replaces the old placeholder-style precondition view with the
actually proved surfaces currently available:

* direct R3 closed-graph promotion;
* concrete Hilbert/dense/closed/unbounded operator preconditions;
* graph-form symmetry;
* formal adjoint containment `T ⊆ T*`;
* formal-adjoint graph agreement with the completed diagonal graph;
* formal-adjoint domain carrier agreement;
* formal-adjoint coordinate-value agreement.

It is still deliberately below Mathlib adjoint construction, reverse containment
as a Mathlib adjoint theorem, resolvent/deficiency control, essential
self-adjointness, self-adjointness, spectral theorem, PVM, exact atom, and
positive spectral weight. -/
def concreteL2R4VerifiedSelfAdjointnessPreconditionPacket : Prop :=
  concreteAnalyticSpineL2R3ToR4SelfAdjointnessPreconditionHandoffReady ∧
  concreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditionsReady ∧
  concreteAnalyticSpineL2R2SymmetricOperatorSurfaceReady ∧
  concreteAnalyticSpineL2R2AdjointContainmentSurfaceReady ∧
  concreteL2R2CompletedDiagonalGraphSymmetric ∧
  concreteL2R2CompletedDiagonalFormalAdjointContainment ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  ((concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule :
      Set (lp (fun _ : ℕ => ℝ) 2)) =
    concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ (y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule) (n : ℕ),
    concreteL2R2CompletedDiagonalFormalAdjointLinearMap y n =
      concreteL2DiagonalWeight n * y.1 n)

/-- The verified R4 pre-self-adjointness evidence packet is ready. -/
theorem concrete_l2_r4_verified_self_adjointness_precondition_packet_ready :
    concreteL2R4VerifiedSelfAdjointnessPreconditionPacket := by
  exact ⟨
    concrete_analytic_spine_l2_r3_to_r4_self_adjointness_precondition_handoff_ready,
    concrete_analytic_spine_l2_r2_self_adjointness_concrete_preconditions_ready,
    concrete_analytic_spine_l2_r2_symmetric_operator_surface_ready,
    concrete_analytic_spine_l2_r2_adjoint_containment_surface_ready,
    concrete_l2_r2_completed_diagonal_graph_symmetric,
    concrete_l2_r2_completed_diagonal_formal_adjoint_containment,
    concrete_l2_r2_formal_adjoint_linear_map_graph_pointwise_agrees_completed_diagonal,
    concrete_l2_r2_formal_adjoint_graph_candidate_pointwise_agrees_completed_diagonal,
    concrete_l2_r2_formal_adjoint_submodule_domain_agrees_candidate,
    concrete_l2_r2_formal_adjoint_linear_map_coordinate_value_agrees_diagonal⟩

/-- R4 verified pre-self-adjointness boundary.

The evidence packet is strong enough to start the Mathlib adjoint/self-adjointness
lane, but it is not yet the lane's theorem. -/
def concreteL2R4VerifiedSelfAdjointnessPreconditionBoundary : Prop :=
  concreteL2R4VerifiedSelfAdjointnessPreconditionPacket ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSpectralTheorem ∧
  concreteL2R2ClosedOperatorBoundaryNotPVM ∧
  concreteL2R2ClosedOperatorBoundaryNotPositiveSpectralWeight

/-- The R4 verified pre-self-adjointness boundary is ready. -/
theorem concrete_l2_r4_verified_self_adjointness_precondition_boundary_ready :
    concreteL2R4VerifiedSelfAdjointnessPreconditionBoundary := by
  exact ⟨
    concrete_l2_r4_verified_self_adjointness_precondition_packet_ready,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_spectral_theorem,
    concrete_l2_r2_closed_operator_boundary_not_pvm,
    concrete_l2_r2_closed_operator_boundary_not_positive_spectral_weight⟩

/-- Public readiness surface for the verified R4 pre-self-adjointness evidence
packet. -/
def concreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacketReady : Prop :=
  concreteL2R4VerifiedSelfAdjointnessPreconditionPacket ∧
  concreteL2R4VerifiedSelfAdjointnessPreconditionBoundary

/-- The public verified R4 pre-self-adjointness evidence packet is ready. -/
theorem concrete_analytic_spine_l2_r4_verified_self_adjointness_precondition_packet_ready :
    concreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacketReady := by
  exact ⟨
    concrete_l2_r4_verified_self_adjointness_precondition_packet_ready,
    concrete_l2_r4_verified_self_adjointness_precondition_boundary_ready⟩

end

end MathlibAnalytic
end MGAP4D
