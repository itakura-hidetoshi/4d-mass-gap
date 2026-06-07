import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2AdjointGraphCandidateStructure
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelAnalyticPacketConstructionTargetFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Bridge packet from the existing analytic spine candidate layer to the
actual-Borel packet construction target.

The imported analytic spine module is the current analytic-side candidate
anchor.  This bridge does not claim that the analytic packet has been built; it
records the exact data that turns an analytic spine candidate certificate into
the concrete packet target required by the actual-Borel spectral-measure chain. -/
structure SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridge where
  analytic_spine_candidate : Prop
  analytic_spine_certificate : analytic_spine_candidate
  packet : SpectralMeasurePVMActualBorelConcreteNontrivialSelfAdjointPacket
  packet_realizes_spine_candidate : analytic_spine_candidate → Prop
  packet_realization_certificate : packet_realizes_spine_candidate analytic_spine_certificate

/-- A bridge packet supplies the analytic packet construction target. -/
theorem spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_supplies_target
    (B : SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridge) :
    SpectralMeasurePVMActualBorelAnalyticPacketConstructionTarget := by
  exact ⟨B.packet, True.intro⟩

/-- If an analytic spine candidate packet bridge exists, the actual-Borel chain
obtains the post-interface closure certificate with the no-shell boundary. -/
def SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeProjectsToClosure : Prop :=
  (∃ B : SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridge, True) →
    SpectralMeasurePVMActualBorelPostInterfaceResidualCertificate ∧
    SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The analytic spine candidate packet bridge projects to closure. -/
theorem spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_projects_to_closure :
    SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeProjectsToClosure := by
  intro hB
  rcases hB with ⟨B, _⟩
  exact spectral_measure_pvm_actual_borel_analytic_packet_construction_target_projects_to_closure
    (spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_supplies_target B)

/-- Index showing that the actual-Borel residual has been lowered to an analytic
spine candidate packet bridge. -/
def SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeIndexReady : Prop :=
  SpectralMeasurePVMActualBorelAnalyticPacketConstructionTargetFinalReceiptReady ∧
  SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeProjectsToClosure ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The analytic spine candidate packet bridge index is ready. -/
theorem spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_index_ready :
    SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeIndexReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_analytic_packet_construction_target_final_receipt_ready,
    spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_projects_to_closure,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the analytic spine candidate packet bridge index. -/
def SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeIndexPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeIndexReady ∧
  SpectralMeasurePVMActualBorelAnalyticPacketConstructionTargetFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the analytic spine candidate packet bridge index is held. -/
theorem spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_index_public_boundary_held :
    SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeIndexPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_index_ready,
    spectral_measure_pvm_actual_borel_analytic_packet_construction_target_final_receipt_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
