import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableChainIndex

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Final receipt for R5 compact centered plaquette observable construction. -/
def CompactCenteredPlaquetteObservableFinalReceiptReady : Prop :=
  CompactCenteredPlaquetteObservableChainIndexReady ∧
  CompactCenteredPlaquetteObservableChainIndexPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableConstructionReceiptReady ∧
  CompactCenteredPlaquetteObservableConstructionTarget ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final receipt for R5 compact centered plaquette observable construction is ready. -/
theorem compact_centered_plaquette_observable_final_receipt_ready :
    CompactCenteredPlaquetteObservableFinalReceiptReady := by
  exact ⟨
    compact_centered_plaquette_observable_chain_index_ready,
    compact_centered_plaquette_observable_chain_index_public_boundary_held,
    compact_centered_plaquette_observable_construction_receipt_ready,
    compact_centered_plaquette_observable_construction_target_ready,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for R5 final receipt. -/
def CompactCenteredPlaquetteObservableFinalReceiptPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableChainIndexPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R5 final receipt is held. -/
theorem compact_centered_plaquette_observable_final_receipt_public_boundary_held :
    CompactCenteredPlaquetteObservableFinalReceiptPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_final_receipt_ready,
    compact_centered_plaquette_observable_chain_index_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
