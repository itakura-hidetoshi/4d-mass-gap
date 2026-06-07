import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroClosedSubrouteChainIndexFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Root-facing final export for the closed Dirac-zero actual-Borel R4 subroute.

This is the safe export surface for upper R4 layers: the closed Dirac-zero
subroute is available as a theorem/receipt bundle, but it is exported only with
the no-shell-to-full-collapse barrier, so it cannot be used as a proof of the
full nontrivial Yang--Mills operator route. -/
def SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingFinalExportReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteFinalReceiptReady ∧
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteChainIndexReady ∧
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteTheorem ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The root-facing final export for the closed Dirac-zero actual-Borel R4
subroute is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_root_facing_final_export_ready :
    SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingFinalExportReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_final_receipt_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_final_receipt_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_chain_index_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_theorem,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Root-facing exported theorem surface for upper R4 layers.

This is intentionally weaker than a global R4 discharge: it exports only the
closed Dirac-zero theorem package plus its boundary. -/
def SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingTheoremSurface : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingFinalExportReady ∧
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroClosedSubroutePublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The root-facing exported theorem surface for the Dirac-zero subroute is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_root_facing_theorem_surface :
    SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingTheoremSurface := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_root_facing_final_export_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the root-facing final export for the closed Dirac-zero
actual-Borel subroute. -/
def SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingFinalExportPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingTheoremSurface ∧
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the root-facing final export is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_root_facing_final_export_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingFinalExportPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_root_facing_theorem_surface,
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_final_receipt_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
