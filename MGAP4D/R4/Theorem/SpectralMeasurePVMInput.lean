import MGAP4D.R3.Theorem.SelfAdjointClosureBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 spectral-measure/PVM input packet in the seven-stage analytic roadmap.

R3 is actual self-adjointness.  R4 starts from that closed self-adjoint operator
input and opens the spectral-measure/PVM construction target.  R4 input does not
include exact atom membership, the numeric value `33 / 20`, or positive spectral
weight; those belong to R6 and R7. -/
def SpectralMeasurePVMInputPacket : Prop :=
  R3.Theorem.SelfAdjointClosureBridgeReady ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.IsClosed MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap =
    MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap

/-- The R4 spectral-measure/PVM input packet is ready. -/
theorem spectral_measure_pvm_input_packet_ready :
    SpectralMeasurePVMInputPacket := by
  exact ⟨
    R3.Theorem.self_adjoint_closure_bridge_ready,
    R3.Theorem.r3_self_adjoint_operator_ready,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self⟩

/-- R4 spectral-measure/PVM boundary.

R4 has acquired the actual self-adjoint input.  The concrete spectral measure,
concrete PVM, normalization, projection-valuedness, countable additivity, and
spectral theorem compatibility remain R4 obligations. -/
def SpectralMeasurePVMBoundary : Prop :=
  SpectralMeasurePVMInputPacket ∧
  True

/-- The R4 spectral-measure/PVM boundary is ready. -/
theorem spectral_measure_pvm_boundary_ready :
    SpectralMeasurePVMBoundary := by
  exact ⟨spectral_measure_pvm_input_packet_ready, trivial⟩

/-- Public readiness predicate for R4 input in the seven-stage analytic roadmap. -/
def SpectralMeasurePVMInputReady : Prop :=
  SpectralMeasurePVMInputPacket ∧ SpectralMeasurePVMBoundary

/-- R4 spectral-measure/PVM input is ready. -/
theorem spectral_measure_pvm_input_ready :
    SpectralMeasurePVMInputReady := by
  exact ⟨spectral_measure_pvm_input_packet_ready, spectral_measure_pvm_boundary_ready⟩

/-- Short alias: R4 has the actual self-adjoint operator input required for
spectral measure/PVM construction. -/
theorem r4_self_adjoint_operator_input_ready :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact R3.Theorem.r3_self_adjoint_operator_ready

end

end Theorem
end R4
end MGAP4D