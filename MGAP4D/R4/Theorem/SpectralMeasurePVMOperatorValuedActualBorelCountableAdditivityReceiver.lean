import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelCountableAdditivityHandoffPacket

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Receiver packet on the genuine operator-topology countable-additivity side.

It accepts the actual-Borel handoff packet as data and records that the genuine
operator-topology countable-additivity bridge is available but still open. -/
structure SpectralMeasurePVMActualBorelCountableAdditivityReceiver where
  handoff : SpectralMeasurePVMActualBorelCountableAdditivityHandoffPacket
  accepted_handoff : SpectralMeasurePVMActualBorelCountableAdditivityHandoffPacketTarget
  genuine_bridge_ready :
    SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady
  genuine_countable_additivity_open :
    SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen
  no_shell_collapse : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Receiver for the empty-family actual-Borel countable-additivity handoff. -/
def spectralMeasurePVMActualBorelEmptyCountableAdditivityReceiver :
    SpectralMeasurePVMActualBorelCountableAdditivityReceiver where
  handoff := spectralMeasurePVMActualBorelEmptyCountableAdditivityHandoffPacket
  accepted_handoff :=
    spectral_measure_pvm_actual_borel_countable_additivity_handoff_packet_target_ready
  genuine_bridge_ready :=
    spectral_measure_pvm_operator_valued_genuine_operator_topology_countable_additivity_bridge_ready
  genuine_countable_additivity_open :=
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready
  no_shell_collapse := spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready

/-- Receiver existence target. -/
def SpectralMeasurePVMActualBorelCountableAdditivityReceiverExistenceTarget : Prop :=
  Nonempty SpectralMeasurePVMActualBorelCountableAdditivityReceiver

/-- The receiver exists. -/
theorem spectral_measure_pvm_actual_borel_countable_additivity_receiver_existence_target_ready :
    SpectralMeasurePVMActualBorelCountableAdditivityReceiverExistenceTarget := by
  exact ⟨spectralMeasurePVMActualBorelEmptyCountableAdditivityReceiver⟩

/-- Receiver target tying the actual-Borel handoff to the genuine countable-additivity bridge. -/
def SpectralMeasurePVMActualBorelCountableAdditivityReceiverTarget : Prop :=
  SpectralMeasurePVMActualBorelCountableAdditivityReceiverExistenceTarget ∧
  SpectralMeasurePVMActualBorelCountableAdditivityHandoffPacketPublicBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The receiver target is ready. -/
theorem spectral_measure_pvm_actual_borel_countable_additivity_receiver_target_ready :
    SpectralMeasurePVMActualBorelCountableAdditivityReceiverTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_additivity_receiver_existence_target_ready,
    spectral_measure_pvm_actual_borel_countable_additivity_handoff_packet_public_boundary_held,
    spectral_measure_pvm_operator_valued_genuine_operator_topology_countable_additivity_bridge_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Actual-Borel countable-additivity receiver bridge. -/
def SpectralMeasurePVMActualBorelCountableAdditivityReceiverBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelCountableAdditivityHandoffPacketPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelCountableAdditivityReceiverTarget ∧
  SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel countable-additivity receiver bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_countable_additivity_receiver_bridge_ready :
    SpectralMeasurePVMActualBorelCountableAdditivityReceiverBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_additivity_handoff_packet_public_boundary_held,
    spectral_measure_pvm_actual_borel_countable_additivity_receiver_target_ready,
    spectral_measure_pvm_operator_valued_genuine_operator_topology_countable_additivity_bridge_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel countable-additivity receiver bridge. -/
def SpectralMeasurePVMActualBorelCountableAdditivityReceiverPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelCountableAdditivityReceiverBridgeReady ∧
  SpectralMeasurePVMActualBorelCountableAdditivityReceiverTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the receiver bridge is held. -/
theorem spectral_measure_pvm_actual_borel_countable_additivity_receiver_public_boundary_held :
    SpectralMeasurePVMActualBorelCountableAdditivityReceiverPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_additivity_receiver_bridge_ready,
    spectral_measure_pvm_actual_borel_countable_additivity_receiver_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
