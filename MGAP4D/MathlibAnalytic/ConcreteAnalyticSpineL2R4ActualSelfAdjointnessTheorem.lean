import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacket
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 actual self-adjointness theorem packet.

The earlier R4 file only packaged verified preconditions for the
Mathlib-adjoint/self-adjointness lane.  This packet is the additive theorem layer:
it imports the verified R4 precondition packet and then records the actual
Mathlib `LinearPMap` adjoint equality and `IsSelfAdjoint` theorem for the dense
diagonal operator.  Spectral theorem, PVM construction, and positive spectral
weight remain downstream lanes. -/
def concreteL2R4ActualSelfAdjointnessTheoremPacket : Prop :=
  concreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacketReady ∧
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady ∧
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady ∧
  Dense ((concreteL2R2DenseDiagonalDomainLinearPMap.domain :
    Set ConcreteL2R1HilbertCarrier)) ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint =
    concreteL2R2DenseDiagonalDomainLinearPMap.graph ∧
  (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).graph =
    concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint

/-- R4 actual self-adjointness theorem packet is ready. -/
theorem concrete_l2_r4_actual_self_adjointness_theorem_packet_ready :
    concreteL2R4ActualSelfAdjointnessTheoremPacket := by
  exact ⟨
    concrete_analytic_spine_l2_r4_verified_self_adjointness_precondition_packet_ready,
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready,
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_adjoint_eq_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_graph_eq_graph_adjoint⟩

/-- R4 actual self-adjointness theorem boundary.

This closes the old R4 boundary marker `boundaryNotSelfAdjointness` for the dense
`LinearPMap` lane.  It intentionally does not close spectral theorem, concrete
PVM, or positive spectral-weight construction. -/
def concreteL2R4ActualSelfAdjointnessTheoremBoundary : Prop :=
  concreteL2R4ActualSelfAdjointnessTheoremPacket ∧
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryFullSpectralTheoremStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPVMStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPositiveSpectralWeightStillSeparate

/-- R4 actual self-adjointness theorem boundary is ready. -/
theorem concrete_l2_r4_actual_self_adjointness_theorem_boundary_ready :
    concreteL2R4ActualSelfAdjointnessTheoremBoundary := by
  exact ⟨
    concrete_l2_r4_actual_self_adjointness_theorem_packet_ready,
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready,
    trivial,
    trivial,
    trivial⟩

/-- Public readiness predicate for R4 actual self-adjointness. -/
def concreteAnalyticSpineL2R4ActualSelfAdjointnessTheoremReady : Prop :=
  concreteL2R4ActualSelfAdjointnessTheoremPacket ∧
  concreteL2R4ActualSelfAdjointnessTheoremBoundary

/-- R4 actual self-adjointness is proved. -/
theorem concrete_analytic_spine_l2_r4_actual_self_adjointness_theorem_ready :
    concreteAnalyticSpineL2R4ActualSelfAdjointnessTheoremReady := by
  exact ⟨
    concrete_l2_r4_actual_self_adjointness_theorem_packet_ready,
    concrete_l2_r4_actual_self_adjointness_theorem_boundary_ready⟩

/-- Short theorem alias: the R4 dense diagonal `LinearPMap` is actually
self-adjoint in Mathlib. -/
theorem concrete_l2_r4_dense_diagonal_linear_pmap_isSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint

end

end MathlibAnalytic
end MGAP4D