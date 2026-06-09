import MGAP4D.R6.Theorem.ExactAtom3320R5Handoff

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Reviewer-facing open marker for the numeric value-origin gap in the current
R6 lane.

The current R6 exact-atom route reaches atom membership and observable/PVM mass
compatibility.  It does not use the carrier equality
`exactGapValueReal = 33 / 20` as part of the R6 target, and it does not yet prove
that the concrete spectrum forces the numeric value `33 / 20`. -/
def ExactAtom3320SpectralValueDerivationStillOpenAtR6Origin : Prop := True

/-- The spectral value-origin gap is still open at this R6 origin surface. -/
theorem exact_atom_3320_spectral_value_derivation_still_open_at_r6_origin_ready :
    ExactAtom3320SpectralValueDerivationStillOpenAtR6Origin := by
  trivial

/-- Origin certificate for the R6 observable-atom/PVM compatibility lane.

This packages the part that is mathematically meaningful at the current R6
stage: R5 handoff, observable atom review surface, membership of the chosen value
in the atom, compatibility with PVM mass, and the open marker for the unresolved
numeric spectral-origin step.

It deliberately does not include `exactGapValueReal = (33 : ℝ) / 20`. -/
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
  ExactAtom3320SpectralValueDerivationStillOpenAtR6Origin ∧
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
    exact_atom_3320_spectral_value_derivation_still_open_at_r6_origin_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 target: observable-atom membership and PVM-mass compatibility are carried
forward while the genuine numeric spectral derivation remains open.

The target deliberately does not assert `exactGapValueReal = (33 : ℝ) / 20`. -/
def ExactAtom3320NonDefinitionalDerivationTarget : Prop :=
  ExactAtom3320NonDefinitionalOriginCertificate ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  ExactAtom3320SpectralValueDerivationStillOpenAtR6Origin ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 observable-atom/PVM compatibility target is ready. -/
theorem exact_atom_3320_nondefinitional_derivation_target_ready :
    ExactAtom3320NonDefinitionalDerivationTarget := by
  exact ⟨
    exact_atom_3320_nondefinitional_origin_certificate_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    exact_atom_3320_spectral_value_derivation_still_open_at_r6_origin_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Legacy carrier equality export retained only for compatibility with older
terminal surfaces.

This theorem is outside the R6 target above and must not be used as the numeric
source for a spectral derivation. -/
theorem exact_atom_3320_value_eq :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.exact_value_eq_3320

end

end Theorem
end R6
end MGAP4D
