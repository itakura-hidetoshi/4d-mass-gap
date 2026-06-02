import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacket
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoff

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 self-adjoint input bridge.

R4 itself is the exact lower-bound/operator-order layer.  It does not own the
spectral theorem or PVM construction.  This bridge records that the
self-adjointness input required by the R4 operator-order receipt is now supplied
by the concrete dense diagonal Mathlib `LinearPMap` lane. -/
def SelfAdjointInputBridgePacket : Prop :=
  MathlibAnalytic.concreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacketReady ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady ∧
  Dense ((MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap.domain :
    Set MathlibAnalytic.ConcreteL2R1HilbertCarrier)) ∧
  LinearPMap.IsClosed MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap =
    MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint =
    MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap.graph

/-- The R4 self-adjoint input bridge is ready. -/
theorem self_adjoint_input_bridge_packet_ready :
    SelfAdjointInputBridgePacket := by
  exact ⟨
    MathlibAnalytic.concrete_analytic_spine_l2_r4_verified_self_adjointness_precondition_packet_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph⟩

/-- R4 boundary after the self-adjoint input bridge.

The R4 self-adjoint input is closed.  R4 lower-bound/operator-order receipts are
separate from R5 spectral/PVM construction. -/
def SelfAdjointInputBridgeBoundary : Prop :=
  SelfAdjointInputBridgePacket ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryFullSpectralTheoremStillSeparate ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPVMStillSeparate ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPositiveSpectralWeightStillSeparate

/-- The R4 self-adjoint input bridge boundary is ready. -/
theorem self_adjoint_input_bridge_boundary_ready :
    SelfAdjointInputBridgeBoundary := by
  exact ⟨
    self_adjoint_input_bridge_packet_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready,
    trivial,
    trivial,
    trivial⟩

/-- Public readiness predicate for the R4 self-adjoint input bridge. -/
def SelfAdjointInputBridgeReady : Prop :=
  SelfAdjointInputBridgePacket ∧ SelfAdjointInputBridgeBoundary

/-- The R4 self-adjoint input bridge is ready. -/
theorem self_adjoint_input_bridge_ready :
    SelfAdjointInputBridgeReady := by
  exact ⟨self_adjoint_input_bridge_packet_ready, self_adjoint_input_bridge_boundary_ready⟩

/-- Short alias: the self-adjoint input needed by R4 is supplied. -/
theorem r4_self_adjoint_input_supplied :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint

end

end Theorem
end R4
end MGAP4D