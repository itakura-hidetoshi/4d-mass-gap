import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacket
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoff

namespace MGAP4D
namespace R3
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R3 self-adjoint closure bridge in the seven-stage analytic roadmap.

R3 is the actual self-adjointness stage.  This bridge records that the concrete
dense diagonal Mathlib `LinearPMap` lane supplies dense domain, closed graph,
actual adjoint equality, and `IsSelfAdjoint`.  R4 then starts from the resulting
spectral/PVM input. -/
def SelfAdjointClosureBridgePacket : Prop :=
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

/-- The R3 self-adjoint closure bridge is ready. -/
theorem self_adjoint_closure_bridge_packet_ready :
    SelfAdjointClosureBridgePacket := by
  exact ⟨
    MathlibAnalytic.concrete_analytic_spine_l2_r4_verified_self_adjointness_precondition_packet_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph⟩

/-- R3 boundary after self-adjoint closure.

The R3 self-adjointness stage is closed.  R4 spectral theorem, concrete PVM, and
positive spectral-weight construction remain downstream obligations. -/
def SelfAdjointClosureBridgeBoundary : Prop :=
  SelfAdjointClosureBridgePacket ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryFullSpectralTheoremStillSeparate ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPVMStillSeparate ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPositiveSpectralWeightStillSeparate

/-- The R3 self-adjoint closure bridge boundary is ready. -/
theorem self_adjoint_closure_bridge_boundary_ready :
    SelfAdjointClosureBridgeBoundary := by
  exact ⟨
    self_adjoint_closure_bridge_packet_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready,
    trivial,
    trivial,
    trivial⟩

/-- Public readiness predicate for R3 self-adjoint closure. -/
def SelfAdjointClosureBridgeReady : Prop :=
  SelfAdjointClosureBridgePacket ∧ SelfAdjointClosureBridgeBoundary

/-- The R3 self-adjoint closure bridge is ready. -/
theorem self_adjoint_closure_bridge_ready :
    SelfAdjointClosureBridgeReady := by
  exact ⟨self_adjoint_closure_bridge_packet_ready, self_adjoint_closure_bridge_boundary_ready⟩

/-- Short alias: the R3 dense diagonal operator is self-adjoint. -/
theorem r3_self_adjoint_operator_ready :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint

end

end Theorem
end R3
end MGAP4D