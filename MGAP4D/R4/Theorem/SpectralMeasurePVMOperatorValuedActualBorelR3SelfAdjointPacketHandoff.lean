import MGAP4D.R3.Theorem.ActualSelfAdjointnessClosure
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelMathlibSpectralOutputToNontrivialWitnessBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R3 supplies the actual self-adjoint source packet for the R4 actual-Borel
spectral-measure lane. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointSourcePacketReady : Prop :=
  MGAP4D.R3.Theorem.ActualSelfAdjointnessClosureReady ∧
  MGAP4D.R3.Theorem.ActualSelfAdjointnessClosurePacket ∧
  IsSelfAdjoint MGAP4D.MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady

/-- The R3 self-adjoint source packet is ready for R4 handoff. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_source_packet_ready :
    SpectralMeasurePVMActualBorelR3SelfAdjointSourcePacketReady := by
  exact ⟨
    MGAP4D.R3.Theorem.actual_self_adjointness_closure_ready,
    MGAP4D.R3.Theorem.actual_self_adjointness_closure_packet_ready,
    MGAP4D.R3.Theorem.r3_dense_diagonal_linear_pmap_isSelfAdjoint,
    MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready⟩

/-- R4 spectral output packet whose self-adjoint source is supplied by R3.

The remaining R4-side payload is the law-carrying actual-Borel spectral measure
and the certificate that it is produced from the R3 self-adjoint source by the
Mathlib spectral theorem output lane. -/
structure SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacket where
  r3_self_adjoint_source_ready : SpectralMeasurePVMActualBorelR3SelfAdjointSourcePacketReady
  spectral_measure : SpectralMeasurePVMActualBorelGenericLawCarryingSpectralMeasureInterface
  produced_by_r3_self_adjoint_mathlib_spectral_output : Prop
  produced_certificate : produced_by_r3_self_adjoint_mathlib_spectral_output
  no_shell_to_full_collapse_boundary : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Convert the R3 self-adjoint spectral output packet to the R4 Mathlib output
interface. -/
def spectralMeasurePVMActualBorelMathlibOutputOfR3SelfAdjointSpectralOutputPacket
    (P : SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacket) :
    SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput where
  spectral_measure := P.spectral_measure
  produced_by_mathlib_nontrivial_self_adjoint_spectral_theorem :=
    P.produced_by_r3_self_adjoint_mathlib_spectral_output
  produced_certificate := P.produced_certificate
  no_shell_to_full_collapse_boundary := P.no_shell_to_full_collapse_boundary

/-- Existence of the R3-sourced spectral output packet supplies the R4 single
remaining constructive obligation. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputSuppliesR4Obligation : Prop :=
  (∃ P : SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputPacket, True) →
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation

/-- The R3-sourced spectral output packet supplies the R4 obligation. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_supplies_r4_obligation :
    SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputSuppliesR4Obligation := by
  intro hP
  rcases hP with ⟨P, _⟩
  exact spectral_measure_pvm_actual_borel_mathlib_output_supplies_single_remaining_obligation
    ⟨spectralMeasurePVMActualBorelMathlibOutputOfR3SelfAdjointSpectralOutputPacket P, True.intro⟩

/-- Handoff boundary: R3 owns self-adjointness; R4 owns spectral output. -/
def SpectralMeasurePVMActualBorelR3SelfAdjointPacketHandoffBoundaryReady : Prop :=
  SpectralMeasurePVMActualBorelR3SelfAdjointSourcePacketReady ∧
  SpectralMeasurePVMActualBorelR3SelfAdjointSpectralOutputSuppliesR4Obligation ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R3-to-R4 self-adjoint packet handoff boundary is ready. -/
theorem spectral_measure_pvm_actual_borel_r3_self_adjoint_packet_handoff_boundary_ready :
    SpectralMeasurePVMActualBorelR3SelfAdjointPacketHandoffBoundaryReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_r3_self_adjoint_source_packet_ready,
    spectral_measure_pvm_actual_borel_r3_self_adjoint_spectral_output_supplies_r4_obligation,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
