import MGAP4D.R6.Theorem.ExactAtom3320NonDefinitionalDerivation

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Current R6 observable-atom/PVM compatibility route. -/
def ExactAtom3320ObservableAtomPVMCompatibilityRoute : Prop :=
  ExactAtom3320R5HandoffInputReady ∧
  MGAP4D.MathlibAnalytic.observableAtomTheoremTheoremReviewSurface.ready ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.spectralWeight
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom =
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.pvmData.projectionMass
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.pvmData.exactAtom

/-- The observable-atom/PVM compatibility route is ready. -/
theorem exact_atom_3320_observable_atom_pvm_compatibility_route_ready :
    ExactAtom3320ObservableAtomPVMCompatibilityRoute := by
  exact ⟨
    exact_atom_3320_r5_handoff_input_ready,
    MGAP4D.MathlibAnalytic.observable_atom_theorem_theorem_review_surface_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_compatible_with_pvm_mass⟩

/-- R6 non-definitional value-derivation gate.

This gate is intentionally conditional: R6 may derive the displayed `33/20` value
only after the spectral/PVM lane supplies
`ExactAtom3320R6SpectralPVMPinsDerivedValue`.  The theorem body below never
unfolds `exactGapValueReal`; it consumes only the R6 pinning surface. -/
def ExactAtom3320R6SpectralValueDerivationGate : Prop :=
  ExactAtom3320NonDefinitionalDerivationTarget ∧
  (ExactAtom3320R6SpectralPVMPinsDerivedValue →
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
      (33 : ℝ) / 20) ∧
  (ExactAtom3320R6SpectralPVMPinsDerivedValue →
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20)

/-- The R6 non-definitional value-derivation gate is ready. -/
theorem exact_atom_3320_r6_spectral_value_derivation_gate_ready :
    ExactAtom3320R6SpectralValueDerivationGate := by
  exact ⟨
    exact_atom_3320_nondefinitional_derivation_target_ready,
    exact_atom_3320_r6_derived_spectral_value_eq_3320,
    exact_atom_3320_r6_exact_gap_value_eq_3320⟩

/-- Marker that R6 has a guarded, non-definitional route for the displayed value.

This is not an unconditional adoption of `exactGapValueReal = 33/20`; it records
that the value theorem is available exactly when the R6 spectral/PVM pinning
surface is supplied. -/
def ExactAtom3320GenuineSpectralValueDerivedAtR6 : Prop :=
  ExactAtom3320R6SpectralValueDerivationGate

/-- The guarded R6 spectral-value derivation route is ready. -/
theorem exact_atom_3320_genuine_spectral_value_derived_at_r6_ready :
    ExactAtom3320GenuineSpectralValueDerivedAtR6 := by
  exact exact_atom_3320_r6_spectral_value_derivation_gate_ready

/-- Firewall: R6 carries a guarded non-definitional spectral-value derivation gate,
while the full R4 Borel PVM construction boundary remains guarded. -/
def ExactAtom3320SpectralOriginFirewall : Prop :=
  ExactAtom3320ObservableAtomPVMCompatibilityRoute ∧
  ExactAtom3320GenuineSpectralValueDerivedAtR6 ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The spectral-origin firewall is active. -/
theorem exact_atom_3320_spectral_origin_firewall_ready :
    ExactAtom3320SpectralOriginFirewall := by
  exact ⟨
    exact_atom_3320_observable_atom_pvm_compatibility_route_ready,
    exact_atom_3320_genuine_spectral_value_derived_at_r6_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the exact-atom spectral-origin firewall. -/
def ExactAtom3320SpectralOriginPublicBoundaryHeld : Prop :=
  ExactAtom3320SpectralOriginFirewall ∧
  ExactAtom3320GenuineSpectralValueDerivedAtR6

/-- The public boundary for the exact-atom spectral-origin firewall is held. -/
theorem exact_atom_3320_spectral_origin_public_boundary_held :
    ExactAtom3320SpectralOriginPublicBoundaryHeld := by
  exact ⟨
    exact_atom_3320_spectral_origin_firewall_ready,
    exact_atom_3320_genuine_spectral_value_derived_at_r6_ready⟩

end

end Theorem
end R6
end MGAP4D
