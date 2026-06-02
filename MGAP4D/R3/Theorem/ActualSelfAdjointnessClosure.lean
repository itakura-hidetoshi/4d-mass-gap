import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacket
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoff

namespace MGAP4D
namespace R3
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R3 actual self-adjointness closure.

In the seven-stage analytic roadmap, R3 is the actual self-adjointness stage.
This packet records that the concrete dense diagonal Mathlib `LinearPMap` has a
dense domain, is closed, satisfies `T† = T`, and is `IsSelfAdjoint`.  R4 starts
after this closure and is reserved for spectral measure / PVM construction. -/
def ActualSelfAdjointnessClosurePacket : Prop :=
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

/-- The R3 actual self-adjointness closure packet is ready. -/
theorem actual_self_adjointness_closure_packet_ready :
    ActualSelfAdjointnessClosurePacket := by
  exact ⟨
    MathlibAnalytic.concrete_analytic_spine_l2_r4_verified_self_adjointness_precondition_packet_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph⟩

/-- R3-to-R4 boundary after actual self-adjointness closure.

The R3 self-adjointness stage is closed.  The next stage, R4, is the spectral
measure / PVM construction stage and remains separate. -/
def ActualSelfAdjointnessClosureBoundary : Prop :=
  ActualSelfAdjointnessClosurePacket ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryFullSpectralTheoremStillSeparate ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPVMStillSeparate ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPositiveSpectralWeightStillSeparate

/-- The R3 actual self-adjointness closure boundary is ready. -/
theorem actual_self_adjointness_closure_boundary_ready :
    ActualSelfAdjointnessClosureBoundary := by
  exact ⟨
    actual_self_adjointness_closure_packet_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready,
    trivial,
    trivial,
    trivial⟩

/-- Public readiness predicate for R3 actual self-adjointness. -/
def ActualSelfAdjointnessClosureReady : Prop :=
  ActualSelfAdjointnessClosurePacket ∧ ActualSelfAdjointnessClosureBoundary

/-- R3 actual self-adjointness is closed. -/
theorem actual_self_adjointness_closure_ready :
    ActualSelfAdjointnessClosureReady := by
  exact ⟨actual_self_adjointness_closure_packet_ready, actual_self_adjointness_closure_boundary_ready⟩

/-- Short alias: the R3 dense diagonal `LinearPMap` is actually self-adjoint. -/
theorem r3_dense_diagonal_linear_pmap_isSelfAdjoint :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint

end

end Theorem
end R3
end MGAP4D