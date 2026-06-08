import MGAP4D.R6.Theorem.ExactAtom3320R5Handoff

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Origin certificate for the exact atom 33/20 lane.

This packages the 33/20 value as coming through the observable-atom theorem body:
R5 handoff, observable atom review surface, membership of the exact value in the
atom, compatibility with PVM mass, and the exact-value equality. -/
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
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The origin certificate for the exact atom 33/20 lane is ready. -/
theorem exact_atom_3320_nondefinitional_origin_certificate_ready :
    ExactAtom3320NonDefinitionalOriginCertificate := by
  exact ⟨
    exact_atom_3320_r5_handoff_input_ready,
    MGAP4D.MathlibAnalytic.observable_atom_theorem_theorem_review_surface_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_compatible_with_pvm_mass,
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.exact_value_eq_3320,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 target: exact atom 33/20 is derived through the observable atom/PVM mass
lane, not introduced as an isolated final mass-gap release. -/
def ExactAtom3320NonDefinitionalDerivationTarget : Prop :=
  ExactAtom3320NonDefinitionalOriginCertificate ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 exact atom 33/20 non-definitional derivation target is ready. -/
theorem exact_atom_3320_nondefinitional_derivation_target_ready :
    ExactAtom3320NonDefinitionalDerivationTarget := by
  exact ⟨
    exact_atom_3320_nondefinitional_origin_certificate_ready,
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.exact_value_eq_3320,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem for the exact 33/20 value in R6. -/
theorem exact_atom_3320_value_eq :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.exact_value_eq_3320

end

end Theorem
end R6
end MGAP4D
