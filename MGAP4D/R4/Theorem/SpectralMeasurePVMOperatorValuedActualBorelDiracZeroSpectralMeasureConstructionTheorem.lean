import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDiracZeroPVMLawsTheorem
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelTheoremSurfaceAggregateChainIndexFinalReceipt

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Genuine spectral-measure construction theorem for the Dirac-zero actual-Borel
route.

This theorem packages the actual-Borel carrier/surface aggregate together with
the genuine Dirac-zero PVM laws: endpoint normalization, projection laws,
intersection multiplicativity, finite additivity, and concrete `tsum` countable
additivity.  It is not a self-adjoint spectral theorem; it is the concrete
Dirac-zero projection-valued spectral-measure construction on the actual Borel
carrier. -/
def SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem : Prop :=
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexReady ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateFinalReceiptReady ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergenceTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsPublicBoundaryHeld

/-- The Dirac-zero actual-Borel spectral-measure construction theorem is proved. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem :
    SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem := by
  exact ⟨
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_chain_index_ready,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_final_receipt_ready,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_genuine_operator_topology_convergence_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_public_boundary_held⟩

/-- The Dirac-zero actual-Borel route has a genuine spectral-measure construction
while still keeping the self-adjoint spectral-theorem residual separate. -/
def SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionPromotedToGenuineTheorem : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroPVMLawsPromotedToGenuineTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroGenuineOperatorTopologyConvergencePublicBoundaryHeld ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The Dirac-zero actual-Borel spectral-measure construction is promoted to a
genuine theorem. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_promoted_to_genuine_theorem :
    SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionPromotedToGenuineTheorem := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_pvm_laws_promoted_to_genuine_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_genuine_operator_topology_convergence_public_boundary_held,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after promoting the Dirac-zero actual-Borel spectral-measure
construction to a genuine theorem. -/
def SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionPromotedToGenuineTheorem ∧
  SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionTheorem ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after promoting the Dirac-zero actual-Borel spectral-measure
construction is held. -/
theorem spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_public_boundary_held :
    SpectralMeasurePVMActualBorelDiracZeroSpectralMeasureConstructionPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_promoted_to_genuine_theorem,
    spectral_measure_pvm_actual_borel_dirac_zero_spectral_measure_construction_theorem,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
