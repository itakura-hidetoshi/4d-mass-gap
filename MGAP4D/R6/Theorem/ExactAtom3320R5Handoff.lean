import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableLaterStageHandoff
import MGAP4D.MathlibAnalytic.ObservableAtomTheoremTheorem

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 input package: consume the R5 compact centered plaquette observable handoff,
attach the observable atom theorem body, and keep positive spectral weight
deferred to the next stage. -/
def ExactAtom3320R5HandoffInputReady : Prop :=
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableLaterStageHandoffFinalReceiptReady ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableRootFacingEntryReady ∧
  MGAP4D.MathlibAnalytic.observableAtomTheoremTheoremReviewSurface.ready ∧
  MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.ready ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 input handoff from R5 is ready. -/
theorem exact_atom_3320_r5_handoff_input_ready :
    ExactAtom3320R5HandoffInputReady := by
  exact ⟨
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_later_stage_handoff_final_receipt_ready,
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_root_facing_entry_ready,
    MGAP4D.MathlibAnalytic.observable_atom_theorem_theorem_review_surface_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_theorem_data_ready,
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 must not prematurely consume the later positive spectral-weight derivation. -/
def ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary : Prop :=
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R6 does not consume the later positive spectral-weight derivation. -/
theorem exact_atom_3320_does_not_consume_positive_spectral_weight_boundary :
    ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary := by
  exact ⟨
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R6
end MGAP4D
