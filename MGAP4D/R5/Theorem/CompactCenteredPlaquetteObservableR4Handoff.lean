import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelDenseDiagonalPVMSourcedResidualClosureFinalReceipt
import MGAP4D.MathlibAnalytic.CompactPlaquetteConstructionTheorem

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 input package: consume the R4 dense-diagonal PVM-sourced constructive
closure and the existing abstract compact plaquette construction review surface. -/
def CompactCenteredPlaquetteObservableR4HandoffInputReady : Prop :=
  MGAP4D.R4.Theorem.SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedResidualClosureFinalReceiptReady ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMActualBorelDenseDiagonalPVMSourcedResidualClosureFinalReceiptPublicBoundaryHeld ∧
  MGAP4D.MathlibAnalytic.compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R5 handoff input from R4 is ready. -/
theorem compact_centered_plaquette_observable_r4_handoff_input_ready :
    CompactCenteredPlaquetteObservableR4HandoffInputReady := by
  exact ⟨
    MGAP4D.R4.Theorem.spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_residual_closure_final_receipt_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_actual_borel_dense_diagonal_pvm_sourced_residual_closure_final_receipt_public_boundary_held,
    MGAP4D.MathlibAnalytic.compact_plaquette_construction_theorem_review_surface_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R5 must not prematurely consume the later 33/20 atom derivation. -/
def CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary : Prop :=
  MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R5 does not consume the later 33/20 atom derivation. -/
theorem compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary :
    CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary := by
  exact ⟨
    MGAP4D.R4.Theorem.spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R5 must not prematurely consume the later positive spectral-weight derivation. -/
def CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary : Prop :=
  MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R5 does not consume the later positive spectral-weight derivation. -/
theorem compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary :
    CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary := by
  exact ⟨
    MGAP4D.R4.Theorem.spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
