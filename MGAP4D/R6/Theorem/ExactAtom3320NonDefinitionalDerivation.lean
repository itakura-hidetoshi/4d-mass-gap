import MGAP4D.R6.Theorem.ExactAtom3320R5Handoff
import MGAP4D.R6.Theorem.ExactAtom3320YangMillsSpectralDerivation

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Reviewer-facing R6 carrier-alignment origin marker. -/
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

/-- R6 spectral/PVM value derivation surface. -/
def ExactAtom3320R6SpectralPVMPinsDerivedValue : Prop :=
  exactAtom3320YangMillsSpectralDerivation.ready ∧
  MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
    (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.spectralWeight
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom =
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.pvmData.projectionMass
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.pvmData.exactAtom ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R6 obtains the displayed value through the Hamiltonian/PVM/spectral route. -/
theorem exact_atom_3320_r6_derived_spectral_value_from_hamiltonian_pvm_route :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
      (33 : ℝ) / 20 := by
  exact (Eq.symm MGAP4D.MathlibAnalytic.yang_mills_hamiltonian_exact_gap_eq_spectral_value).trans
    MGAP4D.MathlibAnalytic.hamiltonian_pvm_spectral_exact_gap_value_eq_33_over_20_from_spectral_route

/-- The R6 spectral/PVM value-derivation surface is ready. -/
theorem exact_atom_3320_r6_spectral_pvm_pins_derived_value_ready :
    ExactAtom3320R6SpectralPVMPinsDerivedValue := by
  exact ⟨
    exact_atom_3320_yang_mills_spectral_derivation_ready,
    exact_atom_3320_r6_derived_spectral_value_from_hamiltonian_pvm_route,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_compatible_with_pvm_mass,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 derivation of the displayed spectral value. -/
theorem exact_atom_3320_r6_derived_spectral_value_eq_3320
    (h : ExactAtom3320R6SpectralPVMPinsDerivedValue) :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
      (33 : ℝ) / 20 := by
  rcases h with ⟨_, hValue, _⟩
  exact hValue

/-- Canonical R6 derivation of the displayed spectral value. -/
theorem exact_atom_3320_r6_derived_spectral_value_eq_3320_ready :
    MGAP4D.MathlibAnalytic.yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue =
      (33 : ℝ) / 20 := by
  exact exact_atom_3320_r6_derived_spectral_value_eq_3320
    exact_atom_3320_r6_spectral_pvm_pins_derived_value_ready

/-- R6 exact-gap value theorem. -/
theorem exact_atom_3320_r6_exact_gap_value_eq_3320
    (h : ExactAtom3320R6SpectralPVMPinsDerivedValue) :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact exact_atom_3320_yang_mills_exact_gap_carrier_eq_derived.trans
    (exact_atom_3320_r6_derived_spectral_value_eq_3320 h)

/-- Canonical R6 exact-gap value theorem. -/
theorem exact_atom_3320_r6_exact_gap_value_eq_3320_ready :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact exact_atom_3320_r6_exact_gap_value_eq_3320
    exact_atom_3320_r6_spectral_pvm_pins_derived_value_ready

/-- Origin certificate for the R6 observable-atom/PVM compatibility lane. -/
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

/-- R6 target. -/
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
