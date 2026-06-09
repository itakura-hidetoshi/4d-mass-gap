import MGAP4D.R6.Theorem.ExactAtom3320NonDefinitionalDerivation

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Chain index for the R6 observable-atom/PVM compatibility lane. -/
def ExactAtom3320ChainIndexReady : Prop :=
  ExactAtom3320R5HandoffInputReady ∧
  ExactAtom3320NonDefinitionalOriginCertificate ∧
  ExactAtom3320NonDefinitionalDerivationTarget ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  ExactAtom3320SpectralValueDerivationStillOpenAtR6Origin ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 observable-atom/PVM compatibility chain index is ready. -/
theorem exact_atom_3320_chain_index_ready :
    ExactAtom3320ChainIndexReady := by
  exact ⟨
    exact_atom_3320_r5_handoff_input_ready,
    exact_atom_3320_nondefinitional_origin_certificate_ready,
    exact_atom_3320_nondefinitional_derivation_target_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    exact_atom_3320_spectral_value_derivation_still_open_at_r6_origin_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R6 observable-atom/PVM compatibility chain index. -/
def ExactAtom3320ChainIndexPublicBoundaryHeld : Prop :=
  ExactAtom3320ChainIndexReady ∧
  ExactAtom3320SpectralValueDerivationStillOpenAtR6Origin ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R6 observable-atom/PVM compatibility chain index is held. -/
theorem exact_atom_3320_chain_index_public_boundary_held :
    ExactAtom3320ChainIndexPublicBoundaryHeld := by
  exact ⟨
    exact_atom_3320_chain_index_ready,
    exact_atom_3320_spectral_value_derivation_still_open_at_r6_origin_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R6
end MGAP4D
