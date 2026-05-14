import MGAP4D.Hamiltonian.OperatorBody
import MGAP4D.Spectral.LowerBoundProofBody

namespace MGAP4D
namespace Hamiltonian

/-- Named pre-Mathlib targets for constructing the physical eigenvector `psi_*`.

This is the fifth residual-resolution target: expose the proof-body pieces
needed to replace the structural eigen-witness surface by an analytic eigenvector
construction theorem. -/
inductive EigenvectorConstructionTarget where
  | witnessCarrier
  | witnessNormOne
  | witnessOrthogonal
  | witnessNotVacuum
  | witnessInDomain
  | eigenvalue3320
  | eigenRelation
  | upperBoundCompatibility
  | lowerBoundSandwichCompatibility
  deriving Repr, DecidableEq

/-- A pre-Mathlib eigenvector-construction surface for the physical witness
`psi_*`.

The surface records the theorem-body obligations for constructing a normalized
orthogonal non-vacuum eigenvector of `H_phys` with eigenvalue `33/20`.  It is
still structural: the analytic construction is a later replacement target. -/
structure EigenvectorConstructionSurface where
  lowerBoundProofBody : Spectral.LowerBoundProofBodySurface
  lowerBoundProofBodyReady : lowerBoundProofBody.ready
  operatorBody : HphysOperatorBodySurface
  operatorBodyReady : operatorBody.ready
  physicalEigenWitness : PhysicalEigenWitness3320
  physicalEigenWitnessReady : physicalEigenWitness.ready
  witnessCarrierSurface : Prop
  witnessNormOneSurface : physicalEigenWitness.eigenWitness.normOne = true
  witnessOrthogonalSurface : physicalEigenWitness.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuumSurface : physicalEigenWitness.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  witnessInDomainSurface : operatorBody.eigenWitnessInDomainSurface
  eigenvalue3320Surface : physicalEigenWitness.eigenWitness.eigenvalue = 33 / 20
  eigenRelationSurface : physicalEigenWitness.eigenWitness.eigenRelationVisible
  upperBoundCompatibilitySurface : Prop
  lowerBoundSandwichCompatibilitySurface : lowerBoundProofBody.sharpSandwichCompatibilitySurface
  exactGapValue3320 : lowerBoundProofBody.gapInfimum.exactGap.exactGapValue = 33 / 20
  hamiltonianIsHphys : operatorBody.hamiltonian = Hphys
  finalReleaseHeld : lowerBoundProofBody.finalReleaseHeld
  publicBoundaryLocked : lowerBoundProofBody.publicBoundaryLocked
  noAutoRelease : lowerBoundProofBody.noAutoRelease
  theoremBoundaryHeld : lowerBoundProofBody.theoremBoundaryHeld

def EigenvectorConstructionSurface.ready
    (S : EigenvectorConstructionSurface) : Prop :=
  S.lowerBoundProofBodyReady ∧ S.operatorBodyReady ∧ S.physicalEigenWitnessReady ∧
  S.witnessCarrierSurface ∧ S.witnessNormOneSurface ∧ S.witnessOrthogonalSurface ∧
  S.witnessNotVacuumSurface ∧ S.witnessInDomainSurface ∧ S.eigenvalue3320Surface ∧
  S.eigenRelationSurface ∧ S.upperBoundCompatibilitySurface ∧
  S.lowerBoundSandwichCompatibilitySurface ∧ S.exactGapValue3320 ∧
  S.hamiltonianIsHphys ∧ S.finalReleaseHeld ∧ S.publicBoundaryLocked ∧
  S.noAutoRelease ∧ S.theoremBoundaryHeld

def eigenvector3320ConstructionSurface : EigenvectorConstructionSurface :=
  { lowerBoundProofBody := Spectral.lowerBound3320ProofBodySurface
    lowerBoundProofBodyReady := Spectral.lower_bound_3320_proof_body_surface_ready
    operatorBody := hphys3320OperatorBodySurface
    operatorBodyReady := hphys_3320_operator_body_surface_ready
    physicalEigenWitness := physicalEigenWitness3320
    physicalEigenWitnessReady := physical_eigen_witness_3320_ready
    witnessCarrierSurface := True
    witnessNormOneSurface := physical_eigen_witness_3320_norm_one
    witnessOrthogonalSurface := physical_eigen_witness_3320_orthogonal
    witnessNotVacuumSurface := physical_eigen_witness_3320_not_vacuum
    witnessInDomainSurface := hphys_3320_eigen_witness_in_domain_surface
    eigenvalue3320Surface := physical_eigen_witness_3320_eigenvalue
    eigenRelationSurface := by trivial
    upperBoundCompatibilitySurface := True
    lowerBoundSandwichCompatibilitySurface := Spectral.lower_bound_3320_sharp_sandwich_compatibility_surface
    exactGapValue3320 := Spectral.lower_bound_3320_proof_body_exact_value
    hamiltonianIsHphys := hphys_3320_operator_body_is_Hphys
    finalReleaseHeld := Spectral.lower_bound_3320_proof_body_release_held
    publicBoundaryLocked := Spectral.lower_bound_3320_proof_body_public_boundary_locked
    noAutoRelease := Spectral.lower_bound_3320_proof_body_no_auto_release
    theoremBoundaryHeld := by trivial }

theorem eigenvector_construction_surface_pack
    (S : EigenvectorConstructionSurface) :
    S.ready ↔ S.lowerBoundProofBodyReady ∧ S.operatorBodyReady ∧
      S.physicalEigenWitnessReady ∧ S.witnessCarrierSurface ∧ S.witnessNormOneSurface ∧
      S.witnessOrthogonalSurface ∧ S.witnessNotVacuumSurface ∧ S.witnessInDomainSurface ∧
      S.eigenvalue3320Surface ∧ S.eigenRelationSurface ∧ S.upperBoundCompatibilitySurface ∧
      S.lowerBoundSandwichCompatibilitySurface ∧ S.exactGapValue3320 ∧
      S.hamiltonianIsHphys ∧ S.finalReleaseHeld ∧ S.publicBoundaryLocked ∧
      S.noAutoRelease ∧ S.theoremBoundaryHeld := by
  rfl

theorem eigenvector_3320_construction_surface_ready :
    eigenvector3320ConstructionSurface.ready := by
  exact And.intro Spectral.lower_bound_3320_proof_body_surface_ready <|
    And.intro hphys_3320_operator_body_surface_ready <|
    And.intro physical_eigen_witness_3320_ready <|
    And.intro True.intro <|
    And.intro physical_eigen_witness_3320_norm_one <|
    And.intro physical_eigen_witness_3320_orthogonal <|
    And.intro physical_eigen_witness_3320_not_vacuum <|
    And.intro hphys_3320_eigen_witness_in_domain_surface <|
    And.intro physical_eigen_witness_3320_eigenvalue <|
    And.intro (by trivial) <|
    And.intro True.intro <|
    And.intro Spectral.lower_bound_3320_sharp_sandwich_compatibility_surface <|
    And.intro Spectral.lower_bound_3320_proof_body_exact_value <|
    And.intro hphys_3320_operator_body_is_Hphys <|
    And.intro Spectral.lower_bound_3320_proof_body_release_held <|
    And.intro Spectral.lower_bound_3320_proof_body_public_boundary_locked <|
    And.intro Spectral.lower_bound_3320_proof_body_no_auto_release True.intro

theorem eigenvector_3320_construction_norm_one :
    eigenvector3320ConstructionSurface.physicalEigenWitness.eigenWitness.normOne = true := by
  exact physical_eigen_witness_3320_norm_one

theorem eigenvector_3320_construction_eigenvalue :
    eigenvector3320ConstructionSurface.physicalEigenWitness.eigenWitness.eigenvalue = 33 / 20 := by
  exact physical_eigen_witness_3320_eigenvalue

theorem eigenvector_3320_construction_orthogonal :
    eigenvector3320ConstructionSurface.physicalEigenWitness.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal := by
  exact physical_eigen_witness_3320_orthogonal

theorem eigenvector_3320_construction_not_vacuum :
    eigenvector3320ConstructionSurface.physicalEigenWitness.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum := by
  exact physical_eigen_witness_3320_not_vacuum

theorem eigenvector_3320_construction_in_domain_surface :
    eigenvector3320ConstructionSurface.witnessInDomainSurface := by
  exact hphys_3320_eigen_witness_in_domain_surface

theorem eigenvector_3320_construction_eigen_relation_surface :
    eigenvector3320ConstructionSurface.eigenRelationSurface := by
  trivial

theorem eigenvector_3320_construction_upper_bound_compatibility_surface :
    eigenvector3320ConstructionSurface.upperBoundCompatibilitySurface := by
  trivial

theorem eigenvector_3320_construction_lower_bound_sandwich_compatibility_surface :
    eigenvector3320ConstructionSurface.lowerBoundSandwichCompatibilitySurface := by
  exact Spectral.lower_bound_3320_sharp_sandwich_compatibility_surface

theorem eigenvector_3320_construction_exact_value :
    eigenvector3320ConstructionSurface.lowerBoundProofBody.gapInfimum.exactGap.exactGapValue = 33 / 20 := by
  exact Spectral.lower_bound_3320_proof_body_exact_value

theorem eigenvector_3320_construction_release_held :
    eigenvector3320ConstructionSurface.finalReleaseHeld := by
  exact Spectral.lower_bound_3320_proof_body_release_held

theorem eigenvector_3320_construction_public_boundary_locked :
    eigenvector3320ConstructionSurface.publicBoundaryLocked := by
  exact Spectral.lower_bound_3320_proof_body_public_boundary_locked

theorem eigenvector_3320_construction_no_auto_release :
    eigenvector3320ConstructionSurface.noAutoRelease := by
  exact Spectral.lower_bound_3320_proof_body_no_auto_release

end Hamiltonian
end MGAP4D
