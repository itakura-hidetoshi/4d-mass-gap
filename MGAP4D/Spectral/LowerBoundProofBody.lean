import MGAP4D.Spectral.GapInfimumDefinition
import MGAP4D.Spectral.LowerBound

namespace MGAP4D
namespace Spectral

/-- Named pre-Mathlib targets for the lower-bound proof body.

This is the fourth residual-resolution target: expose the proof-body pieces
needed to replace the structural lower-bound surface by the analytic theorem
`Rayleigh(H_phys, psi) >= 33/20` on the normalized orthogonal sector. -/
inductive LowerBoundProofBodyTarget where
  | normalizedOrthogonalStateCarrier
  | rayleighEnergyFunctional
  | positivityEstimate
  | coerciveEstimate
  | lowerBoundValueCompatibility
  | infimumLowerBoundCompatibility
  | sharpSandwichCompatibility
  deriving Repr, DecidableEq

/-- A pre-Mathlib lower-bound proof-body surface.

The surface records the theorem-body obligations for proving that every
normalized orthogonal-sector state has energy at least `33/20`.  It remains a
structural surface only; the analytic inequality proof is a later replacement. -/
structure LowerBoundProofBodySurface where
  gapInfimum : GapInfimumDefinitionSurface
  gapInfimumReady : gapInfimum.ready
  lowerBound : LowerBoundCertificate
  lowerBoundReady : lowerBound.ready
  normalizedOrthogonalStateCarrierSurface : Prop
  rayleighEnergyFunctionalSurface : Prop
  positivityEstimateSurface : Prop
  coerciveEstimateSurface : Prop
  lowerBoundValueCompatibilitySurface : lowerBound.lowerBound.value = 33 / 20
  infimumLowerBoundCompatibilitySurface : gapInfimum.lowerBoundCompatibilitySurface
  sharpSandwichCompatibilitySurface : Prop
  exactGapValue3320 : gapInfimum.exactGap.exactGapValue = 33 / 20
  hamiltonianIsHphys : gapInfimum.operatorBody.hamiltonian = Hamiltonian.Hphys
  finalReleaseHeld : gapInfimum.finalReleaseHeld
  publicBoundaryLocked : gapInfimum.publicBoundaryLocked
  noAutoRelease : gapInfimum.noAutoRelease
  theoremBoundaryHeld : gapInfimum.theoremBoundaryHeld

def LowerBoundProofBodySurface.ready
    (S : LowerBoundProofBodySurface) : Prop :=
  S.gapInfimumReady ∧ S.lowerBoundReady ∧
  S.normalizedOrthogonalStateCarrierSurface ∧ S.rayleighEnergyFunctionalSurface ∧
  S.positivityEstimateSurface ∧ S.coerciveEstimateSurface ∧
  S.lowerBoundValueCompatibilitySurface ∧ S.infimumLowerBoundCompatibilitySurface ∧
  S.sharpSandwichCompatibilitySurface ∧ S.exactGapValue3320 ∧ S.hamiltonianIsHphys ∧
  S.finalReleaseHeld ∧ S.publicBoundaryLocked ∧ S.noAutoRelease ∧
  S.theoremBoundaryHeld

def lowerBound3320ProofBodySurface : LowerBoundProofBodySurface :=
  { gapInfimum := gapInfimum3320DefinitionSurface
    gapInfimumReady := gap_infimum_3320_definition_surface_ready
    lowerBound := lowerBound3320Certificate True True True True
    lowerBoundReady := lower_bound_3320_certificate_ready
    normalizedOrthogonalStateCarrierSurface := True
    rayleighEnergyFunctionalSurface := True
    positivityEstimateSurface := True
    coerciveEstimateSurface := True
    lowerBoundValueCompatibilitySurface := by rfl
    infimumLowerBoundCompatibilitySurface := gap_infimum_3320_lower_bound_compatibility_surface
    sharpSandwichCompatibilitySurface := True
    exactGapValue3320 := gap_infimum_3320_definition_exact_value
    hamiltonianIsHphys := gap_infimum_3320_definition_hamiltonian_is_Hphys
    finalReleaseHeld := gap_infimum_3320_definition_release_held
    publicBoundaryLocked := gap_infimum_3320_definition_public_boundary_locked
    noAutoRelease := gap_infimum_3320_definition_no_auto_release
    theoremBoundaryHeld := by trivial }

theorem lower_bound_proof_body_surface_pack
    (S : LowerBoundProofBodySurface) :
    S.ready ↔ S.gapInfimumReady ∧ S.lowerBoundReady ∧
      S.normalizedOrthogonalStateCarrierSurface ∧ S.rayleighEnergyFunctionalSurface ∧
      S.positivityEstimateSurface ∧ S.coerciveEstimateSurface ∧
      S.lowerBoundValueCompatibilitySurface ∧ S.infimumLowerBoundCompatibilitySurface ∧
      S.sharpSandwichCompatibilitySurface ∧ S.exactGapValue3320 ∧ S.hamiltonianIsHphys ∧
      S.finalReleaseHeld ∧ S.publicBoundaryLocked ∧ S.noAutoRelease ∧
      S.theoremBoundaryHeld := by
  rfl

theorem lower_bound_3320_proof_body_surface_ready :
    lowerBound3320ProofBodySurface.ready := by
  exact And.intro gap_infimum_3320_definition_surface_ready <|
    And.intro lower_bound_3320_certificate_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro rfl <|
    And.intro gap_infimum_3320_lower_bound_compatibility_surface <|
    And.intro True.intro <|
    And.intro gap_infimum_3320_definition_exact_value <|
    And.intro gap_infimum_3320_definition_hamiltonian_is_Hphys <|
    And.intro gap_infimum_3320_definition_release_held <|
    And.intro gap_infimum_3320_definition_public_boundary_locked <|
    And.intro gap_infimum_3320_definition_no_auto_release True.intro

theorem lower_bound_3320_proof_body_exact_value :
    lowerBound3320ProofBodySurface.gapInfimum.exactGap.exactGapValue = 33 / 20 := by
  exact gap_infimum_3320_definition_exact_value

theorem lower_bound_3320_proof_body_lower_bound_value :
    lowerBound3320ProofBodySurface.lowerBound.lowerBound.value = 33 / 20 := by
  rfl

theorem lower_bound_3320_proof_body_hamiltonian_is_Hphys :
    lowerBound3320ProofBodySurface.gapInfimum.operatorBody.hamiltonian = Hamiltonian.Hphys := by
  exact gap_infimum_3320_definition_hamiltonian_is_Hphys

theorem lower_bound_3320_proof_body_release_held :
    lowerBound3320ProofBodySurface.finalReleaseHeld := by
  exact gap_infimum_3320_definition_release_held

theorem lower_bound_3320_proof_body_public_boundary_locked :
    lowerBound3320ProofBodySurface.publicBoundaryLocked := by
  exact gap_infimum_3320_definition_public_boundary_locked

theorem lower_bound_3320_proof_body_no_auto_release :
    lowerBound3320ProofBodySurface.noAutoRelease := by
  exact gap_infimum_3320_definition_no_auto_release

theorem lower_bound_3320_normalized_orthogonal_state_carrier_surface :
    lowerBound3320ProofBodySurface.normalizedOrthogonalStateCarrierSurface := by
  trivial

theorem lower_bound_3320_rayleigh_energy_functional_surface :
    lowerBound3320ProofBodySurface.rayleighEnergyFunctionalSurface := by
  trivial

theorem lower_bound_3320_positivity_estimate_surface :
    lowerBound3320ProofBodySurface.positivityEstimateSurface := by
  trivial

theorem lower_bound_3320_coercive_estimate_surface :
    lowerBound3320ProofBodySurface.coerciveEstimateSurface := by
  trivial

theorem lower_bound_3320_infimum_lower_bound_compatibility_surface :
    lowerBound3320ProofBodySurface.infimumLowerBoundCompatibilitySurface := by
  exact gap_infimum_3320_lower_bound_compatibility_surface

theorem lower_bound_3320_sharp_sandwich_compatibility_surface :
    lowerBound3320ProofBodySurface.sharpSandwichCompatibilitySurface := by
  trivial

end Spectral
end MGAP4D
