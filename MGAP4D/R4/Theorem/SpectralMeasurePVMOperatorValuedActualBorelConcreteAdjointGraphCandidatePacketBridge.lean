import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelAnalyticSpineCandidatePacketBridgeObligationProjection

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete bridge from the existing adjoint graph candidate surface to the
actual-Borel packet target. -/
structure SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridge where
  packet : SpectralMeasurePVMActualBorelConcreteNontrivialSelfAdjointPacket
  packet_realizes_concrete_adjoint_graph_candidate :
    MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady → Prop
  packet_realization_certificate :
    packet_realizes_concrete_adjoint_graph_candidate
      MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_adjoint_graph_candidate_structure_surface_ready

/-- A concrete adjoint graph candidate packet bridge supplies the generic
analytic spine candidate packet bridge. -/
def spectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeOfConcreteAdjointGraphCandidate
    (B : SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridge) :
    SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridge where
  analytic_spine_candidate :=
    MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady
  analytic_spine_certificate :=
    MGAP4D.MathlibAnalytic.concrete_analytic_spine_l2_r2_adjoint_graph_candidate_structure_surface_ready
  packet := B.packet
  packet_realizes_spine_candidate := B.packet_realizes_concrete_adjoint_graph_candidate
  packet_realization_certificate := B.packet_realization_certificate

/-- Existence of the concrete adjoint graph candidate packet bridge supplies the
analytic spine candidate packet bridge obligation. -/
def SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeSuppliesSpineBridgeObligation : Prop :=
  (∃ B : SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridge, True) →
    SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeExistenceObligation

/-- The concrete adjoint graph candidate packet bridge supplies the spine bridge
obligation. -/
theorem spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_supplies_spine_bridge_obligation :
    SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeSuppliesSpineBridgeObligation := by
  intro hB
  rcases hB with ⟨B, _⟩
  exact ⟨
    spectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeOfConcreteAdjointGraphCandidate B,
    True.intro⟩

/-- The concrete adjoint graph candidate packet bridge projects to closure. -/
def SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeProjectsToClosure : Prop :=
  (∃ B : SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridge, True) →
    SpectralMeasurePVMActualBorelPostInterfaceResidualCertificate ∧
    SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete adjoint graph candidate packet bridge projects to the closure package. -/
theorem spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_projects_to_closure :
    SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeProjectsToClosure := by
  intro hB
  exact spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_projects_to_closure
    (spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_supplies_spine_bridge_obligation hB)

/-- Index for the concrete adjoint graph candidate packet bridge. -/
def SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeIndexReady : Prop :=
  SpectralMeasurePVMActualBorelAnalyticSpineCandidatePacketBridgeObligationProjectionReady ∧
  SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeSuppliesSpineBridgeObligation ∧
  SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeProjectsToClosure ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The concrete adjoint graph candidate packet bridge index is ready. -/
theorem spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_index_ready :
    SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeIndexReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_analytic_spine_candidate_packet_bridge_obligation_projection_ready,
    spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_supplies_spine_bridge_obligation,
    spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_projects_to_closure,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
