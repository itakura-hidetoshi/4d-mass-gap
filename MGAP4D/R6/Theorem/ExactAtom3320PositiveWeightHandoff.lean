import MGAP4D.R6.Theorem.ExactAtom3320FinalReceipt

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Handoff surface from R6 exact atom 33/20 derivation to the positive spectral
weight stage. -/
def ExactAtom3320PositiveWeightHandoffReady : Prop :=
  ExactAtom3320FinalReceiptReady ∧
  ExactAtom3320FinalReceiptPublicBoundaryHeld ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  MGAP4D.MathlibAnalytic.observableAtomTheoremTheoremReviewSurface.ready ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The handoff surface from R6 exact atom 33/20 to positive spectral weight is ready. -/
theorem exact_atom_3320_positive_weight_handoff_ready :
    ExactAtom3320PositiveWeightHandoffReady := by
  exact ⟨
    exact_atom_3320_final_receipt_ready,
    exact_atom_3320_final_receipt_public_boundary_held,
    exact_atom_3320_value_eq,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    MGAP4D.MathlibAnalytic.observable_atom_theorem_theorem_review_surface_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem for the next stage. -/
theorem exact_atom_3320_ready_for_positive_spectral_weight_stage :
    ExactAtom3320PositiveWeightHandoffReady := by
  exact exact_atom_3320_positive_weight_handoff_ready

end

end Theorem
end R6
end MGAP4D
