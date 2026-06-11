import MGAP4D.R6.Theorem.ExactAtom3320R5Handoff
import MGAP4D.R6.Theorem.ExactAtom3320YangMillsSpectralDerivation

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Reviewer-facing R6 carrier-alignment origin marker.

R6 carries the observable-atom/PVM lane and the Yang--Mills Hamiltonian spectral
carrier alignment.  It deliberately does **not** export
`exactGapValueReal = (33 : ℝ) / 20`; that theorem is non-adopted until there is a
genuinely non-definitional spectral/PVM derivation. -/
def ExactAtom3320SpectralCarrierAlignedAtR6Origin : Prop :=
  exactAtom3320YangMillsSpectralDerivation.ready ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal =
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  ExactAtom3320YangMillsSpectralValueNonAdoptionAtR6

/-- The R6 carrier-alignment origin marker is ready. -/
theorem exact_atom_3320_spectral_carrier_aligned_at_r6_origin_ready :
    ExactAtom3320SpectralCarrierAlignedAtR6Origin := by
  exact ⟨
    exact_atom_3320_yang_mills_spectral_derivation_ready,
    exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived,
    exact_atom_3320_yang_mills_spectral_value_nonadoption_at_r6_ready⟩

/-- Origin certificate for the R6 observable-atom/PVM compatibility lane.

This packages the R5 handoff, observable atom review surface, membership of the
chosen value in the atom, compatibility with PVM mass, and the R6 carrier
alignment boundary.

It deliberately does not contain a conjunct asserting
`exactGapValueReal = (33 : ℝ) / 20`. -/
def ExactAtom3320NonDefinitionalOriginCertificate : Prop :=
  ExactAtom3320R5HandoffInputReady ∧
  MGAP4D.MathlibAnalytic.observableAtomTheoremTheoremReviewSurface.ready ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.spectralWeight
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom =
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.pvmData.projectionMass
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.pvmData.exactAtom ∧
  ExactAtom3320SpectralCarrierAlignedAtR6Origin ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The origin certificate for the R6 observable-atom/PVM compatibility lane is ready. -/
theorem exact_atom_3320_nondefinitional_origin_certificate_ready :
    ExactAtom3320NonDefinitionalOriginCertificate := by
  exact ⟨
    exact_atom_3320_r5_handoff_input_ready,
    MGAP4D.MathlibAnalytic.observable_atom_theorem_theorem_review_surface_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_compatible_with_pvm_mass,
    exact_atom_3320_spectral_carrier_aligned_at_r6_origin_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 target: observable-atom membership, PVM-mass compatibility, and the R6
Yang--Mills Hamiltonian spectral-carrier alignment are carried forward, while the
displayed value theorem remains non-adopted. -/
def ExactAtom3320NonDefinitionalDerivationTarget : Prop :=
  ExactAtom3320NonDefinitionalOriginCertificate ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  ExactAtom3320SpectralCarrierAlignedAtR6Origin ∧
  ExactAtom3320YangMillsSpectralValueNonAdoptionAtR6 ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 observable-atom/PVM compatibility target is ready. -/
theorem exact_atom_3320_nondefinitional_derivation_target_ready :
    ExactAtom3320NonDefinitionalDerivationTarget := by
  exact ⟨
    exact_atom_3320_nondefinitional_origin_certificate_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    exact_atom_3320_spectral_carrier_aligned_at_r6_origin_ready,
    exact_atom_3320_yang_mills_spectral_value_nonadoption_at_r6_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R6
end MGAP4D
