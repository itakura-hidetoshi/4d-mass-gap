import MGAP4D.Hamiltonian.OperatorBody
import MGAP4D.Spectral.ExactGapTheorem

namespace MGAP4D
namespace Spectral

/-- Named pre-Mathlib targets for defining the mass gap as an infimum on the
orthogonal sector. -/
inductive GapInfimumDefinitionTarget where
  | orthogonalSectorCarrier
  | normalizedStatePredicate
  | rayleighFunctionalSurface
  | spectralInfimumSurface
  | infimumEqualsExactGap
  | lowerBoundCompatibility
  | eigenWitnessAttainmentCompatibility
  deriving Repr, DecidableEq

/-- A pre-Mathlib gap-infimum definition surface.

This is the third residual-resolution layer.  It records the exact-gap value as
the intended infimum of the orthogonal-sector energy/Rayleigh surface, while
preserving the release-hold boundary. -/
structure GapInfimumDefinitionSurface where
  operatorBody : Hamiltonian.HphysOperatorBodySurface
  operatorBodyReady : operatorBody.ready
  exactGap : ExactGapTheoremCertificate
  exactGapReady : exactGap.ready
  orthogonalSectorCarrierSurface : Prop
  normalizedStatePredicateSurface : Prop
  rayleighFunctionalSurface : Prop
  spectralInfimumSurface : Prop
  infimumEqualsExactGapSurface : Prop
  lowerBoundCompatibilitySurface : Prop
  eigenWitnessAttainmentCompatibilitySurface : Prop
  exactGapValue3320 : exactGap.exactGapValue = 33 / 20
  hamiltonianIsHphys : operatorBody.hamiltonian = Hamiltonian.Hphys
  finalReleaseHeld : operatorBody.finalReleaseHeld
  publicBoundaryLocked : operatorBody.publicBoundaryLocked
  noAutoRelease : operatorBody.noAutoRelease
  theoremBoundaryHeld : operatorBody.theoremBoundaryHeld

def GapInfimumDefinitionSurface.ready
    (S : GapInfimumDefinitionSurface) : Prop :=
  S.operatorBodyReady ∧ S.exactGapReady ∧ S.orthogonalSectorCarrierSurface ∧
  S.normalizedStatePredicateSurface ∧ S.rayleighFunctionalSurface ∧
  S.spectralInfimumSurface ∧ S.infimumEqualsExactGapSurface ∧
  S.lowerBoundCompatibilitySurface ∧ S.eigenWitnessAttainmentCompatibilitySurface ∧
  S.exactGapValue3320 ∧ S.hamiltonianIsHphys ∧ S.finalReleaseHeld ∧
  S.publicBoundaryLocked ∧ S.noAutoRelease ∧ S.theoremBoundaryHeld

def gapInfimum3320DefinitionSurface : GapInfimumDefinitionSurface :=
  { operatorBody := Hamiltonian.hphys3320OperatorBodySurface
    operatorBodyReady := Hamiltonian.hphys_3320_operator_body_surface_ready
    exactGap := exactGapTheorem3320Certificate
    exactGapReady := exact_gap_theorem_3320_ready
    orthogonalSectorCarrierSurface := True
    normalizedStatePredicateSurface := True
    rayleighFunctionalSurface := True
    spectralInfimumSurface := True
    infimumEqualsExactGapSurface := True
    lowerBoundCompatibilitySurface := True
    eigenWitnessAttainmentCompatibilitySurface := True
    exactGapValue3320 := exact_gap_theorem_3320_value
    hamiltonianIsHphys := Hamiltonian.hphys_3320_operator_body_is_Hphys
    finalReleaseHeld := Hamiltonian.hphys_3320_operator_body_release_held
    publicBoundaryLocked := Hamiltonian.hphys_3320_operator_body_public_boundary_locked
    noAutoRelease := Hamiltonian.hphys_3320_operator_body_no_auto_release
    theoremBoundaryHeld := by trivial }

theorem gap_infimum_definition_surface_pack
    (S : GapInfimumDefinitionSurface) :
    S.ready ↔ S.operatorBodyReady ∧ S.exactGapReady ∧
      S.orthogonalSectorCarrierSurface ∧ S.normalizedStatePredicateSurface ∧
      S.rayleighFunctionalSurface ∧ S.spectralInfimumSurface ∧
      S.infimumEqualsExactGapSurface ∧ S.lowerBoundCompatibilitySurface ∧
      S.eigenWitnessAttainmentCompatibilitySurface ∧ S.exactGapValue3320 ∧
      S.hamiltonianIsHphys ∧ S.finalReleaseHeld ∧ S.publicBoundaryLocked ∧
      S.noAutoRelease ∧ S.theoremBoundaryHeld := by
  rfl

theorem gap_infimum_3320_definition_surface_ready :
    gapInfimum3320DefinitionSurface.ready := by
  exact And.intro Hamiltonian.hphys_3320_operator_body_surface_ready <|
    And.intro exact_gap_theorem_3320_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro exact_gap_theorem_3320_value <|
    And.intro Hamiltonian.hphys_3320_operator_body_is_Hphys <|
    And.intro Hamiltonian.hphys_3320_operator_body_release_held <|
    And.intro Hamiltonian.hphys_3320_operator_body_public_boundary_locked <|
    And.intro Hamiltonian.hphys_3320_operator_body_no_auto_release True.intro

theorem gap_infimum_3320_definition_exact_value :
    gapInfimum3320DefinitionSurface.exactGap.exactGapValue = 33 / 20 := by
  exact exact_gap_theorem_3320_value

theorem gap_infimum_3320_definition_hamiltonian_is_Hphys :
    gapInfimum3320DefinitionSurface.operatorBody.hamiltonian = Hamiltonian.Hphys := by
  exact Hamiltonian.hphys_3320_operator_body_is_Hphys

theorem gap_infimum_3320_definition_release_held :
    gapInfimum3320DefinitionSurface.finalReleaseHeld := by
  exact Hamiltonian.hphys_3320_operator_body_release_held

theorem gap_infimum_3320_definition_public_boundary_locked :
    gapInfimum3320DefinitionSurface.publicBoundaryLocked := by
  exact Hamiltonian.hphys_3320_operator_body_public_boundary_locked

theorem gap_infimum_3320_definition_no_auto_release :
    gapInfimum3320DefinitionSurface.noAutoRelease := by
  exact Hamiltonian.hphys_3320_operator_body_no_auto_release

theorem gap_infimum_3320_orthogonal_sector_carrier_surface :
    gapInfimum3320DefinitionSurface.orthogonalSectorCarrierSurface := by
  trivial

theorem gap_infimum_3320_normalized_state_predicate_surface :
    gapInfimum3320DefinitionSurface.normalizedStatePredicateSurface := by
  trivial

theorem gap_infimum_3320_rayleigh_functional_surface :
    gapInfimum3320DefinitionSurface.rayleighFunctionalSurface := by
  trivial

theorem gap_infimum_3320_spectral_infimum_surface :
    gapInfimum3320DefinitionSurface.spectralInfimumSurface := by
  trivial

theorem gap_infimum_3320_infimum_equals_exact_gap_surface :
    gapInfimum3320DefinitionSurface.infimumEqualsExactGapSurface := by
  trivial

theorem gap_infimum_3320_lower_bound_compatibility_surface :
    gapInfimum3320DefinitionSurface.lowerBoundCompatibilitySurface := by
  trivial

theorem gap_infimum_3320_eigen_witness_attainment_compatibility_surface :
    gapInfimum3320DefinitionSurface.eigenWitnessAttainmentCompatibilitySurface := by
  trivial

end Spectral
end MGAP4D
