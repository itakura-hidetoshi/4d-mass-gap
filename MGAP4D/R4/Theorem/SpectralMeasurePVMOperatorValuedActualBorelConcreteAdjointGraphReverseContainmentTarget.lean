import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelConcreteAdjointGraphCandidatePacketBridgeFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Witness target for the reverse containment step of the concrete adjoint graph
candidate. -/
structure SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentWitness where
  candidate_surface_ready :
    MGAP4D.MathlibAnalytic.concreteAnalyticSpineL2R2AdjointGraphCandidateStructureSurfaceReady
  reverse_adjoint_containment : Prop
  reverse_adjoint_containment_certificate : reverse_adjoint_containment
  no_shell_to_full_collapse_boundary : SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A reverse-containment witness is the next constructive target after the
concrete adjoint graph candidate final receipt. -/
def SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentTargetReady
    (W : SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentWitness) : Prop :=
  SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeFinalReceiptReady ∧
  W.candidate_surface_ready ∧
  W.reverse_adjoint_containment ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- Any reverse-containment witness supplies the reverse-containment target. -/
theorem spectral_measure_pvm_actual_borel_concrete_adjoint_graph_reverse_containment_target_ready
    (W : SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentWitness) :
    SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentTargetReady W := by
  exact ⟨
    spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_final_receipt_ready,
    W.candidate_surface_ready,
    W.reverse_adjoint_containment_certificate,
    W.no_shell_to_full_collapse_boundary⟩

/-- Existence obligation for the reverse-containment witness. -/
def SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentWitnessExistenceObligation : Prop :=
  ∃ W : SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentWitness,
    SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentTargetReady W

/-- Projection from the reverse-containment witness existence obligation to the
preserved public boundary. -/
def SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentObligationProjectionReady : Prop :=
  SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeFinalReceiptReady ∧
  (SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentWitnessExistenceObligation →
    SpectralMeasurePVMNoShellToFullCollapseBoundary) ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The reverse-containment obligation projection is ready. -/
theorem spectral_measure_pvm_actual_borel_concrete_adjoint_graph_reverse_containment_obligation_projection_ready :
    SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentObligationProjectionReady := by
  refine ⟨
    spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_final_receipt_ready,
    ?_,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩
  intro hW
  rcases hW with ⟨W, htarget⟩
  exact htarget.2.2.2

/-- Public boundary for the reverse-containment target. -/
def SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentTargetPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentObligationProjectionReady ∧
  SpectralMeasurePVMActualBorelConcreteAdjointGraphCandidatePacketBridgeFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the reverse-containment target is held. -/
theorem spectral_measure_pvm_actual_borel_concrete_adjoint_graph_reverse_containment_target_public_boundary_held :
    SpectralMeasurePVMActualBorelConcreteAdjointGraphReverseContainmentTargetPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_concrete_adjoint_graph_reverse_containment_obligation_projection_ready,
    spectral_measure_pvm_actual_borel_concrete_adjoint_graph_candidate_packet_bridge_final_receipt_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
