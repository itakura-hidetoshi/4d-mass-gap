import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableConstructionTarget

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Chain index for R5 compact centered plaquette observable construction. -/
def CompactCenteredPlaquetteObservableChainIndexReady : Prop :=
  CompactCenteredPlaquetteObservableR4HandoffInputReady ∧
  CompactCenteredPlaquetteObservableConstructionTarget ∧
  CompactCenteredPlaquetteObservableConstructionReceiptReady ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R5 compact centered plaquette observable chain index is ready. -/
theorem compact_centered_plaquette_observable_chain_index_ready :
    CompactCenteredPlaquetteObservableChainIndexReady := by
  exact ⟨
    compact_centered_plaquette_observable_r4_handoff_input_ready,
    compact_centered_plaquette_observable_construction_target_ready,
    compact_centered_plaquette_observable_construction_receipt_ready,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R5 compact centered plaquette observable chain index. -/
def CompactCenteredPlaquetteObservableChainIndexPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableChainIndexReady ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R5 chain index is held. -/
theorem compact_centered_plaquette_observable_chain_index_public_boundary_held :
    CompactCenteredPlaquetteObservableChainIndexPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_chain_index_ready,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
