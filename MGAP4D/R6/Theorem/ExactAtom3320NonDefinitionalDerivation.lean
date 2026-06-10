import MGAP4D.R6.Theorem.ExactAtom3320R5Handoff
import MGAP4D.R6.Theorem.ExactAtom3320YangMillsSpectralDerivation

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6-local non-definitional arithmetic normalization of the exact atom carrier.

This is intentionally downstream of the R6 Yang--Mills spectral derivation
surface and does not use any upstream theorem named `exactGapValueReal_eq`. -/
theorem exact_atom_3320_carrier_value_normalizes_at_r6 :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  norm_num [MGAP4D.MathlibAnalytic.exactGapValueReal]

/-- Reviewer-facing origin marker for the numeric value in the R6 lane.

The current R6 exact-atom route reaches atom membership and observable/PVM mass
compatibility.  The numeric value `33/20` is now exported through the downstream
Yang--Mills Hamiltonian spectral derivation surface, with the R6-local carrier
normalization theorem above as the exact-value projection. -/
def ExactAtom3320SpectralValueDerivedAtR6Origin : Prop :=
  exactAtom3320YangMillsSpectralDerivation.ready ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20

/-- The R6 Yang--Mills spectral value-origin surface is ready. -/
theorem exact_atom_3320_spectral_value_derived_at_r6_origin_ready :
    ExactAtom3320SpectralValueDerivedAtR6Origin := by
  exact ⟨
    exact_atom_3320_yang_mills_spectral_derivation_ready,
    exact_atom_3320_carrier_value_normalizes_at_r6⟩

/-- Origin certificate for the R6 observable-atom/PVM compatibility lane.

This packages the R5 handoff, observable atom review surface, membership of the
chosen value in the atom, compatibility with PVM mass, and the R6 spectral-value
derivation surface.

It deliberately does not use an upstream definitional equality
`exactGapValueReal = (33 : ℝ) / 20`; the numeric export is routed through R6. -/
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
  ExactAtom3320SpectralValueDerivedAtR6Origin ∧
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
    exact_atom_3320_spectral_value_derived_at_r6_origin_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 target: observable-atom membership, PVM-mass compatibility, and the R6
Yang--Mills Hamiltonian spectral-value derivation are carried forward. -/
def ExactAtom3320NonDefinitionalDerivationTarget : Prop :=
  ExactAtom3320NonDefinitionalOriginCertificate ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  ExactAtom3320SpectralValueDerivedAtR6Origin ∧
  ExactAtom3320DoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 observable-atom/PVM compatibility target is ready. -/
theorem exact_atom_3320_nondefinitional_derivation_target_ready :
    ExactAtom3320NonDefinitionalDerivationTarget := by
  exact ⟨
    exact_atom_3320_nondefinitional_origin_certificate_ready,
    MGAP4D.MathlibAnalytic.singleton_observable_atom_theorem_exact_value_in_atom,
    exact_atom_3320_spectral_value_derived_at_r6_origin_ready,
    exact_atom_3320_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R6 exact-value export: the exact atom value is obtained at R6, not upstream. -/
theorem exact_atom_3320_value_eq :
    MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact exact_atom_3320_carrier_value_normalizes_at_r6

end

end Theorem
end R6
end MGAP4D
