import MGAP4D.Hamiltonian.OperatorBody

namespace MGAP4D

/-- Bridge from the exact-gap structural realization layer to the `H_phys`
operator-body surface.

This is the second residual-resolution step after structural surface realization:
it connects the exact-gap residual spine to the named operator-body obligations
for dense domain, domain membership, self-adjointness surface, semiboundedness
surface, and eigen-witness typing.  It does not assert that the final public
release is open; the public boundary and final-release hold are preserved. -/
structure ExactGapHphysOperatorBodyBridge where
  structuralSurface : ExactGapStructuralSurfaceRealization
  operatorBody : Hamiltonian.HphysOperatorBodySurface
  structuralSurfaceReady : structuralSurface.ready
  operatorBodyReady : operatorBody.ready
  sameStructuralSurface : operatorBody.structuralSurface = structuralSurface
  hamiltonianIsHphys : operatorBody.hamiltonian = Hamiltonian.Hphys
  physicalEigenWitnessReady : operatorBody.physicalEigenWitness.ready
  denseDomainSurface : operatorBody.denseDomainSurface
  vacuumInDomainSurface : operatorBody.vacuumInDomainSurface
  orthogonalSectorAdmissibleSurface : operatorBody.orthogonalSectorAdmissibleSurface
  selfAdjointSurface : operatorBody.selfAdjointSurface
  semiboundedBelowSurface : operatorBody.semiboundedBelowSurface
  eigenWitnessInDomainSurface : operatorBody.eigenWitnessInDomainSurface
  eigenRelationWellTypedSurface : operatorBody.eigenRelationWellTypedSurface
  exactGapValue3320 : structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20
  finalReleaseHeld : structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld
  publicBoundaryLocked : structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked
  noAutoRelease : structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease
  theoremBoundaryHeld : structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld

/-- Ready predicate for the `H_phys` operator-body bridge.

The predicate expands propositions rather than placing proof fields in type
position.  This keeps the bridge robust under `autoImplicit=false` and avoids the
recent proof-field-as-type failure mode. -/
def ExactGapHphysOperatorBodyBridge.ready
    (B : ExactGapHphysOperatorBodyBridge) : Prop :=
  B.structuralSurface.ready ∧ B.operatorBody.ready ∧
  B.operatorBody.structuralSurface = B.structuralSurface ∧
  B.operatorBody.hamiltonian = Hamiltonian.Hphys ∧
  B.operatorBody.physicalEigenWitness.ready ∧
  B.operatorBody.denseDomainSurface ∧ B.operatorBody.vacuumInDomainSurface ∧
  B.operatorBody.orthogonalSectorAdmissibleSurface ∧ B.operatorBody.selfAdjointSurface ∧
  B.operatorBody.semiboundedBelowSurface ∧ B.operatorBody.eigenWitnessInDomainSurface ∧
  B.operatorBody.eigenRelationWellTypedSurface ∧
  B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
  B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
  B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
  B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld

/-- The concrete `33/20` bridge from exact-gap structural realization to the
`H_phys` operator-body surface. -/
def exactGap3320HphysOperatorBodyBridge : ExactGapHphysOperatorBodyBridge :=
  { structuralSurface := exactGap3320StructuralSurfaceRealization
    operatorBody := Hamiltonian.hphys3320OperatorBodySurface
    structuralSurfaceReady := exact_gap_3320_structural_surface_realization_ready
    operatorBodyReady := Hamiltonian.hphys_3320_operator_body_surface_ready
    sameStructuralSurface := by rfl
    hamiltonianIsHphys := Hamiltonian.hphys_3320_operator_body_is_Hphys
    physicalEigenWitnessReady := Hamiltonian.physical_eigen_witness_3320_ready
    denseDomainSurface := Hamiltonian.hphys_3320_dense_domain_surface
    vacuumInDomainSurface := Hamiltonian.hphys_3320_vacuum_in_domain_surface
    orthogonalSectorAdmissibleSurface := Hamiltonian.hphys_3320_orthogonal_sector_admissible_surface
    selfAdjointSurface := Hamiltonian.hphys_3320_self_adjoint_surface
    semiboundedBelowSurface := Hamiltonian.hphys_3320_semibounded_below_surface
    eigenWitnessInDomainSurface := Hamiltonian.hphys_3320_eigen_witness_in_domain_surface
    eigenRelationWellTypedSurface := Hamiltonian.hphys_3320_eigen_relation_well_typed_surface
    exactGapValue3320 := exact_gap_3320_structural_surface_value
    finalReleaseHeld := exact_gap_3320_structural_surface_release_held
    publicBoundaryLocked := exact_gap_3320_structural_surface_public_boundary_locked
    noAutoRelease := exact_gap_3320_structural_surface_no_auto_release
    theoremBoundaryHeld := exactGap3320StructuralSurfaceRealization.theoremBoundaryHeld }

theorem exact_gap_hphys_operator_body_bridge_pack
    (B : ExactGapHphysOperatorBodyBridge) :
    B.ready ↔ B.structuralSurface.ready ∧ B.operatorBody.ready ∧
      B.operatorBody.structuralSurface = B.structuralSurface ∧
      B.operatorBody.hamiltonian = Hamiltonian.Hphys ∧
      B.operatorBody.physicalEigenWitness.ready ∧
      B.operatorBody.denseDomainSurface ∧ B.operatorBody.vacuumInDomainSurface ∧
      B.operatorBody.orthogonalSectorAdmissibleSurface ∧ B.operatorBody.selfAdjointSurface ∧
      B.operatorBody.semiboundedBelowSurface ∧ B.operatorBody.eigenWitnessInDomainSurface ∧
      B.operatorBody.eigenRelationWellTypedSurface ∧
      B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
      B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
      B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
      B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
      B.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld := by
  rfl

theorem exact_gap_3320_hphys_operator_body_bridge_ready :
    exactGap3320HphysOperatorBodyBridge.ready := by
  exact And.intro exactGap3320HphysOperatorBodyBridge.structuralSurfaceReady <|
    And.intro exactGap3320HphysOperatorBodyBridge.operatorBodyReady <|
    And.intro exactGap3320HphysOperatorBodyBridge.sameStructuralSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.hamiltonianIsHphys <|
    And.intro exactGap3320HphysOperatorBodyBridge.physicalEigenWitnessReady <|
    And.intro exactGap3320HphysOperatorBodyBridge.denseDomainSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.vacuumInDomainSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.orthogonalSectorAdmissibleSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.selfAdjointSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.semiboundedBelowSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.eigenWitnessInDomainSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.eigenRelationWellTypedSurface <|
    And.intro exactGap3320HphysOperatorBodyBridge.exactGapValue3320 <|
    And.intro exactGap3320HphysOperatorBodyBridge.finalReleaseHeld <|
    And.intro exactGap3320HphysOperatorBodyBridge.publicBoundaryLocked <|
    And.intro exactGap3320HphysOperatorBodyBridge.noAutoRelease
      exactGap3320HphysOperatorBodyBridge.theoremBoundaryHeld

theorem exact_gap_3320_hphys_operator_body_bridge_value :
    exactGap3320HphysOperatorBodyBridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 := by
  exact exactGap3320HphysOperatorBodyBridge.exactGapValue3320

theorem exact_gap_3320_hphys_operator_body_bridge_release_held :
    exactGap3320HphysOperatorBodyBridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld := by
  exact exactGap3320HphysOperatorBodyBridge.finalReleaseHeld

theorem exact_gap_3320_hphys_operator_body_bridge_public_boundary_locked :
    exactGap3320HphysOperatorBodyBridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked := by
  exact exactGap3320HphysOperatorBodyBridge.publicBoundaryLocked

theorem exact_gap_3320_hphys_operator_body_bridge_no_auto_release :
    exactGap3320HphysOperatorBodyBridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease := by
  exact exactGap3320HphysOperatorBodyBridge.noAutoRelease

theorem exact_gap_3320_hphys_operator_body_bridge_self_adjoint_surface :
    exactGap3320HphysOperatorBodyBridge.operatorBody.selfAdjointSurface := by
  exact exactGap3320HphysOperatorBodyBridge.selfAdjointSurface

theorem exact_gap_3320_hphys_operator_body_bridge_semibounded_surface :
    exactGap3320HphysOperatorBodyBridge.operatorBody.semiboundedBelowSurface := by
  exact exactGap3320HphysOperatorBodyBridge.semiboundedBelowSurface

end MGAP4D
