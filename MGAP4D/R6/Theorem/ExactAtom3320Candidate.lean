import MGAP4D.R6.Theorem.ExactAtom3320R5Handoff

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 exact atom 33/20 candidate.

This is a typed witness for the exact atom value lane.  It deliberately does not
claim positive spectral weight; that is preserved for the later stage. -/
structure ExactAtom3320Candidate where
  input_ready : ExactAtom3320R5HandoffInputReady
  atom_value : ℚ
  atom_value_eq_3320 : atom_value = (33 : ℚ) / (20 : ℚ)
  sourced_from_r5_compact_centered_plaquette :
    MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableLaterStageHandoffFinalReceiptReady
  does_not_consume_positive_weight : ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary
  no_shell_to_full_collapse_boundary :
    MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The canonical R6 exact atom 33/20 candidate. -/
def exactAtom3320Candidate : ExactAtom3320Candidate where
  input_ready := exact_atom_3320_r5_handoff_input_ready
  atom_value := (33 : ℚ) / (20 : ℚ)
  atom_value_eq_3320 := rfl
  sourced_from_r5_compact_centered_plaquette :=
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_later_stage_handoff_final_receipt_ready
  does_not_consume_positive_weight :=
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary
  no_shell_to_full_collapse_boundary :=
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready

/-- The canonical R6 atom candidate has exact value 33/20. -/
theorem exact_atom_3320_candidate_value_eq_3320 :
    exactAtom3320Candidate.atom_value = (33 : ℚ) / (20 : ℚ) := by
  exact exactAtom3320Candidate.atom_value_eq_3320

/-- The R6 exact atom 33/20 candidate exists. -/
theorem exact_atom_3320_candidate_exists :
    Nonempty ExactAtom3320Candidate := by
  exact ⟨exactAtom3320Candidate⟩

end

end Theorem
end R6
end MGAP4D
