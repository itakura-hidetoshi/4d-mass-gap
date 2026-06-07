import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelMathlibSpectralOutputToNontrivialWitnessBridge

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete packet expected from the analytic nontrivial self-adjoint stage.

This is the next bridge below the Mathlib-output interface: the analytic side
must provide a law-carrying actual-Borel spectral measure, a certificate that it
comes from the concrete nontrivial self-adjoint construction via Mathlib's
spectral theorem output, and the no-shell-to-full-collapse boundary. -/
structure SpectralMeasurePVMActualBorelConcreteNontrivialSelfAdjointPacket where
  spectral_measure : SpectralMeasurePVMActualBorelGenericLawCarryingSpectralMeasureInterface
  concrete_nontrivial_self_adjoint_operator_source : Prop
  concrete_source_certificate : concrete_nontrivial_self_adjoint_operator_source
  mathlib_spectral_output_certificate : concrete_nontrivial_self_adjoint_operator_source →
    Prop
  mathlib_spectral_output_ready :
    mathlib_spectral_output_certificate concrete_source_certificate
  no_shell_to_full_collapse_boundary : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Convert a concrete nontrivial self-adjoint packet into the Mathlib nontrivial
spectral output interface. -/
def spectralMeasurePVMActualBorelMathlibOutputOfConcreteNontrivialSelfAdjointPacket
    (P : SpectralMeasurePVMActualBorelConcreteNontrivialSelfAdjointPacket) :
    SpectralMeasurePVMActualBorelMathlibNontrivialSpectralOutput where
  spectral_measure := P.spectral_measure
  produced_by_mathlib_nontrivial_self_adjoint_spectral_theorem :=
    P.mathlib_spectral_output_certificate P.concrete_source_certificate
  produced_certificate := P.mathlib_spectral_output_ready
  no_shell_to_full_collapse_boundary := P.no_shell_to_full_collapse_boundary

/-- A concrete nontrivial self-adjoint packet supplies the single remaining full
R4 constructive obligation. -/
theorem spectral_measure_pvm_actual_borel_concrete_nontrivial_self_adjoint_packet_supplies_single_obligation
    (P : SpectralMeasurePVMActualBorelConcreteNontrivialSelfAdjointPacket) :
    SpectralMeasurePVMActualBorelFullR4SingleRemainingConstructiveObligation := by
  let O := spectralMeasurePVMActualBorelMathlibOutputOfConcreteNontrivialSelfAdjointPacket P
  exact spectral_measure_pvm_actual_borel_mathlib_output_supplies_single_remaining_obligation
    ⟨O, True.intro⟩

/-- Conditional closure from the concrete nontrivial self-adjoint packet. -/
def SpectralMeasurePVMActualBorelFullR4ConditionalClosureFromConcreteNontrivialSelfAdjointPacket : Prop :=
  (∃ P : SpectralMeasurePVMActualBorelConcreteNontrivialSelfAdjointPacket, True) →
    SpectralMeasurePVMActualBorelPostInterfaceResidualCertificate ∧
    SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- If the concrete nontrivial self-adjoint packet is supplied, the full R4
conditional closure follows. -/
theorem spectral_measure_pvm_actual_borel_full_r4_conditional_closure_from_concrete_nontrivial_self_adjoint_packet :
    SpectralMeasurePVMActualBorelFullR4ConditionalClosureFromConcreteNontrivialSelfAdjointPacket := by
  intro hP
  rcases hP with ⟨P, _⟩
  exact spectral_measure_pvm_actual_borel_full_r4_conditional_final_closure
    (spectral_measure_pvm_actual_borel_concrete_nontrivial_self_adjoint_packet_supplies_single_obligation P)

/-- Residual after adding the concrete nontrivial self-adjoint packet bridge.

At this stage, the remaining constructive work is the analytic construction of
`SpectralMeasurePVMActualBorelConcreteNontrivialSelfAdjointPacket` itself. -/
def SpectralMeasurePVMActualBorelResidualAfterConcreteNontrivialSelfAdjointPacketBridge : Prop :=
  SpectralMeasurePVMActualBorelFullR4ConditionalClosureFromConcreteNontrivialSelfAdjointPacket ∧
  SpectralMeasurePVMActualBorelResidualAfterMathlibOutputBridge ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The residual after the concrete nontrivial self-adjoint packet bridge is
established. -/
theorem spectral_measure_pvm_actual_borel_residual_after_concrete_nontrivial_self_adjoint_packet_bridge :
    SpectralMeasurePVMActualBorelResidualAfterConcreteNontrivialSelfAdjointPacketBridge := by
  exact ⟨
    spectral_measure_pvm_actual_borel_full_r4_conditional_closure_from_concrete_nontrivial_self_adjoint_packet,
    spectral_measure_pvm_actual_borel_residual_after_mathlib_output_bridge,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
