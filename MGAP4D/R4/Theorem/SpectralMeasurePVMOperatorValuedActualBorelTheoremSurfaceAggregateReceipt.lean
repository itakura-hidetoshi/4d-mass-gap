import MGAP4D.R4.TheoremSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Theorem-surface aggregate receipt for the actual-Borel sigma-carrier handoff.

This file sits *outside* `TheoremSurface`: it imports the aggregate surface and
then reads the actual-Borel sigma-carrier aggregate-safe receipt from that
surface.  Thus it certifies the new import route without adding a reverse import
back into `TheoremSurface`. -/
def SpectralMeasurePVMActualBorelTheoremSurfaceAggregateReceiptReady : Prop :=
  SpectralMeasurePVMActualBorelSigmaCarrierHandoffAggregateSafeReceiptReady ∧
  SpectralMeasurePVMActualBorelSigmaCarrierHandoffAggregateSafeReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSigmaCarrierHandoffRootFacingFinalExportIndexReady ∧
  SpectralMeasurePVMActualBorelSigmaCarrierHandoffRootExportFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelSigmaCarrierHandoffChainIndexFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelR4CompletionBoundaryHandoffSigmaCarrierHandoffPhaseSurfaceReady ∧
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel theorem-surface aggregate receipt is ready. -/
theorem spectral_measure_pvm_actual_borel_theorem_surface_aggregate_receipt_ready :
    SpectralMeasurePVMActualBorelTheoremSurfaceAggregateReceiptReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_sigma_carrier_handoff_aggregate_safe_receipt_ready,
    spectral_measure_pvm_actual_borel_sigma_carrier_handoff_aggregate_safe_receipt_public_boundary_held,
    spectral_measure_pvm_actual_borel_sigma_carrier_handoff_root_facing_final_export_index_ready,
    spectral_measure_pvm_actual_borel_sigma_carrier_handoff_root_export_final_receipt_public_boundary_held,
    spectral_measure_pvm_actual_borel_sigma_carrier_handoff_chain_index_final_receipt_public_boundary_held,
    spectral_measure_pvm_actual_borel_r4_completion_boundary_handoff_sigma_carrier_handoff_phase_surface_ready,
    spectral_measure_pvm_operator_valued_r4_completion_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the theorem-surface aggregate receipt.

The boundary makes explicit that importing the actual-Borel aggregate-safe
receipt into `TheoremSurface` does not collapse the still-open genuine spectral
measure construction. -/
def SpectralMeasurePVMActualBorelTheoremSurfaceAggregateReceiptPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateReceiptReady ∧
  SpectralMeasurePVMActualBorelSigmaCarrierHandoffAggregateSafeReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the actual-Borel theorem-surface aggregate receipt is
held. -/
theorem spectral_measure_pvm_actual_borel_theorem_surface_aggregate_receipt_public_boundary_held :
    SpectralMeasurePVMActualBorelTheoremSurfaceAggregateReceiptPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_receipt_ready,
    spectral_measure_pvm_actual_borel_sigma_carrier_handoff_aggregate_safe_receipt_public_boundary_held,
    spectral_measure_pvm_operator_valued_r4_completion_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
