import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroTopLevelSafeReceiver

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Anti-collapse guard for the closed Dirac-zero actual-Borel subroute.

The top-level safe surface may expose the closed zero-operator theorem package,
but the package must remain separated from the global nontrivial R4 discharge by
the no-shell-to-full-collapse boundary. -/
def SpectralMeasurePVMActualBorelDiracZeroAntiCollapseGuardReady : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroTopLevelSafeTheoremSurface ∧
  SpectralMeasurePVMActualBorelDiracZeroTopLevelSafeReceiverPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteRootFacingFinalExportPublicBoundaryHeld ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The anti-collapse guard for the closed Dirac-zero actual-Borel subroute is ready. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_anti_collapse_guard_ready :
    SpectralMeasurePVMActualBorelDiracZeroAntiCollapseGuardReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_top_level_safe_theorem_surface,
    spectral_measure_pvm_actual_borel_dirac_zero_top_level_safe_receiver_public_boundary_held,
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_root_facing_final_export_public_boundary_held,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Safe-use theorem for the closed Dirac-zero actual-Borel subroute.

This is the theorem upper layers should import: it gives the closed Dirac-zero
subroute together with the anti-collapse guard, not a full global R4 discharge. -/
def SpectralMeasurePVMActualBorelDiracZeroSafeUseTheorem : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroClosedSubrouteTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroAntiCollapseGuardReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The safe-use theorem for the closed Dirac-zero actual-Borel subroute is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_safe_use_theorem :
    SpectralMeasurePVMActualBorelDiracZeroSafeUseTheorem := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_closed_subroute_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_anti_collapse_guard_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Final public boundary for safe use of the closed Dirac-zero actual-Borel
subroute. -/
def SpectralMeasurePVMActualBorelDiracZeroSafeUsePublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSafeUseTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroAntiCollapseGuardReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final public boundary for safe use of the closed Dirac-zero subroute is
held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_safe_use_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSafeUsePublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_safe_use_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_anti_collapse_guard_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
