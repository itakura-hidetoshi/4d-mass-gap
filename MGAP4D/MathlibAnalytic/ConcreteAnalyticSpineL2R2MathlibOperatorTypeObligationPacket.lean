import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointMathlibBoundary
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

def concreteL2R2OperatorEncodingTypeObligation : Prop :=
  concreteL2R2CompletedDiagonalGraphDefinedOperator.domainCarrier =
    concreteL2R2CompletedDiagonalOperatorDomainCarrier ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalGraphCarrier

theorem concrete_l2_r2_operator_encoding_type_obligation_ready :
    concreteL2R2OperatorEncodingTypeObligation := by
  exact ⟨rfl, rfl⟩

def concreteL2R2DomainEncodingTypeObligation : Prop :=
  ∀ x : lp (fun _ : ℕ => ℝ) 2,
    x ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.domainCarrier ↔
      ∃ y : lp (fun _ : ℕ => ℝ) 2,
        (x, y) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier

theorem concrete_l2_r2_domain_encoding_type_obligation_ready :
    concreteL2R2DomainEncodingTypeObligation := by
  intro x
  exact concreteL2R2CompletedDiagonalGraphDefinedOperator.graphDomainProjectionLaw x

def concreteL2R2ClosedOperatorApiTypeObligation : Prop :=
  concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady ∧
  ∃ D : Set (lp (fun _ : ℕ => ℝ) 2),
    D = concreteL2R2CompletedDiagonalGraphDefinedOperator.domainCarrier ∧
  ∃ G : Set ((lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2)),
    G = concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
    ∀ x : lp (fun _ : ℕ => ℝ) 2,
      x ∈ D ↔ ∃ y : lp (fun _ : ℕ => ℝ) 2, (x, y) ∈ G

theorem concrete_l2_r2_closed_operator_api_type_obligation_ready :
    concreteL2R2ClosedOperatorApiTypeObligation := by
  refine ⟨
    concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready,
    concreteL2R2CompletedDiagonalGraphDefinedOperator.domainCarrier,
    rfl,
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier,
    rfl,
    ?_⟩
  intro x
  exact concreteL2R2CompletedDiagonalGraphDefinedOperator.graphDomainProjectionLaw x

def concreteL2R2AdjointApiTypeObligation : Prop :=
  concreteAnalyticSpineL2R2FormalAdjointMathlibBoundarySurfaceReady ∧
  ∃ A : Set ((lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2)),
    A = concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier = A ∧
    concreteL2R2FormalAdjointBoundaryNotMathlibAdjointIdentifier ∧
    concreteL2R2FormalAdjointBoundaryNotMathlibIsSelfAdjointTheorem

theorem concrete_l2_r2_adjoint_api_type_obligation_ready :
    concreteL2R2AdjointApiTypeObligation := by
  refine ⟨
    concrete_analytic_spine_l2_r2_formal_adjoint_mathlib_boundary_surface_ready,
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate,
    rfl,
    ?_,
    concrete_l2_r2_formal_adjoint_boundary_not_mathlib_adjoint_identifier,
    concrete_l2_r2_formal_adjoint_boundary_not_mathlib_isSelfAdjoint_theorem⟩
  exact concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate

def concreteL2R2MathlibOperatorTypeNoBridgeClaim : Prop :=
  True

theorem concrete_l2_r2_mathlib_operator_type_no_bridge_claim :
    concreteL2R2MathlibOperatorTypeNoBridgeClaim := by
  trivial

structure ConcreteL2R2MathlibOperatorTypeObligationPacket where
  formalAdjointBoundaryReady :
    concreteAnalyticSpineL2R2FormalAdjointMathlibBoundarySurfaceReady
  closedOperatorTheoremObligationReady :
    concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady
  operatorEncodingTypeObligation : concreteL2R2OperatorEncodingTypeObligation
  domainEncodingTypeObligation : concreteL2R2DomainEncodingTypeObligation
  closedOperatorApiTypeObligation : concreteL2R2ClosedOperatorApiTypeObligation
  adjointApiTypeObligation : concreteL2R2AdjointApiTypeObligation
  noBridgeClaim : concreteL2R2MathlibOperatorTypeNoBridgeClaim

def concreteL2R2MathlibOperatorTypeObligationPacket :
    ConcreteL2R2MathlibOperatorTypeObligationPacket :=
  { formalAdjointBoundaryReady :=
      concrete_analytic_spine_l2_r2_formal_adjoint_mathlib_boundary_surface_ready
    closedOperatorTheoremObligationReady :=
      concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready
    operatorEncodingTypeObligation :=
      concrete_l2_r2_operator_encoding_type_obligation_ready
    domainEncodingTypeObligation :=
      concrete_l2_r2_domain_encoding_type_obligation_ready
    closedOperatorApiTypeObligation :=
      concrete_l2_r2_closed_operator_api_type_obligation_ready
    adjointApiTypeObligation :=
      concrete_l2_r2_adjoint_api_type_obligation_ready
    noBridgeClaim := concrete_l2_r2_mathlib_operator_type_no_bridge_claim }

def concreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacketReady : Prop :=
  concreteAnalyticSpineL2R2FormalAdjointMathlibBoundarySurfaceReady ∧
  concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady ∧
  concreteL2R2OperatorEncodingTypeObligation ∧
  concreteL2R2DomainEncodingTypeObligation ∧
  concreteL2R2ClosedOperatorApiTypeObligation ∧
  concreteL2R2AdjointApiTypeObligation ∧
  concreteL2R2MathlibOperatorTypeNoBridgeClaim

theorem concrete_analytic_spine_l2_r2_mathlib_operator_type_obligation_packet_ready :
    concreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacketReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_formal_adjoint_mathlib_boundary_surface_ready,
    concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready,
    concrete_l2_r2_operator_encoding_type_obligation_ready,
    concrete_l2_r2_domain_encoding_type_obligation_ready,
    concrete_l2_r2_closed_operator_api_type_obligation_ready,
    concrete_l2_r2_adjoint_api_type_obligation_ready,
    concrete_l2_r2_mathlib_operator_type_no_bridge_claim⟩

end

end MathlibAnalytic
end MGAP4D
