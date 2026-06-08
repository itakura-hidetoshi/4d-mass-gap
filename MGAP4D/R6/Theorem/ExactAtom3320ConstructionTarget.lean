import MGAP4D.R6.Theorem.ExactAtom3320Candidate

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 construction target for the exact atom 33/20 lane. -/
def ExactAtom3320ConstructionTarget : Prop :=
  ExactAtom3320R5HandoffInputReady ∧
  Nonempty ExactAtom3320Candidate ∧
  exactAtom3320Candidate.atom_value = (33 : ℚ) / (20 : ℚ) ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableLaterStageHandoffFinalReceiptReady ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 exact atom 33/20 construction target is ready. -/
theorem exact_atom_3320_construction_target_ready :
    ExactAtom3320ConstructionTarget := by
  exact ⟨
    exact_atom_3320_r5_handoff_input_ready,
    exact_atom_3320_candidate_exists,
    exact_atom_3320_candidate_value_eq_3320,
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_later_stage_handoff_final_receipt_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 construction receipt for exact atom 33/20. -/
def ExactAtom3320ConstructionReceiptReady : Prop :=
  ExactAtom3320ConstructionTarget ∧
  Nonempty ExactAtom3320Candidate ∧
  exactAtom3320Candidate.atom_value = (33 : ℚ) / (20 : ℚ) ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 exact atom 33/20 construction receipt is ready. -/
theorem exact_atom_3320_construction_receipt_ready :
    ExactAtom3320ConstructionReceiptReady := by
  exact ⟨
    exact_atom_3320_construction_target_ready,
    exact_atom_3320_candidate_exists,
    exact_atom_3320_candidate_value_eq_3320,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R6
end MGAP4D
