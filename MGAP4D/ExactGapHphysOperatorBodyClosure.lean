import MGAP4D.ExactGapHphysOperatorBodyBridge

namespace MGAP4D

/-- Closure target registry for the `H_phys` operator-body bridge.

This is intentionally still a public-boundary preserving closure surface: it
records that the named `H_phys` operator-body obligations have been surfaced and
linked to the exact `33/20` spine, but it does not turn the residual analytic
operator obligations into a final public release. -/
inductive ExactGapHphysOperatorBodyClosureTarget where
  | bridgeReady
  | operatorBodyReady
  | hamiltonianIdentity
  | denseDomain
  | vacuumDomain
  | orthogonalSector
  | selfAdjointSurface
  | semiboundedSurface
  | eigenWitnessDomain
  | eigenRelationTyped
  | exactGapValue
  | releaseHold
  | publicBoundaryLock
  | noAutoRelease
  | theoremBoundaryHold
  deriving Repr, DecidableEq

/-- Closed handoff packet for the `H_phys` operator-body surface.

The packet gives the next theorem-body stage one stable object to import.  Its
proof fields are all propositions, not proof fields used as types. -/
structure ExactGapHphysOperatorBodyClosure where
  bridge : ExactGapHphysOperatorBodyBridge
  bridgeReady : bridge.ready
  operatorBodyReady : bridge.operatorBody.ready
  hamiltonianIsHphys : bridge.operatorBody.hamiltonian = Hamiltonian.Hphys
  denseDomainSurface : bridge.operatorBody.denseDomainSurface
  vacuumInDomainSurface : bridge.operatorBody.vacuumInDomainSurface
  orthogonalSectorAdmissibleSurface : bridge.operatorBody.orthogonalSectorAdmissibleSurface
  selfAdjointSurface : bridge.operatorBody.selfAdjointSurface
  semiboundedBelowSurface : bridge.operatorBody.semiboundedBelowSurface
  eigenWitnessInDomainSurface : bridge.operatorBody.eigenWitnessInDomainSurface
  eigenRelationWellTypedSurface : bridge.operatorBody.eigenRelationWellTypedSurface
  exactGapValue3320 : bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20
  finalReleaseHeld : bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld
  publicBoundaryLocked : bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked
  noAutoRelease : bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease
  theoremBoundaryHeld : bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld

/-- Ready predicate for the closed `H_phys` operator-body handoff. -/
def ExactGapHphysOperatorBodyClosure.ready
    (C : ExactGapHphysOperatorBodyClosure) : Prop :=
  C.bridge.ready ∧ C.bridge.operatorBody.ready ∧
  C.bridge.operatorBody.hamiltonian = Hamiltonian.Hphys ∧
  C.bridge.operatorBody.denseDomainSurface ∧
  C.bridge.operatorBody.vacuumInDomainSurface ∧
  C.bridge.operatorBody.orthogonalSectorAdmissibleSurface ∧
  C.bridge.operatorBody.selfAdjointSurface ∧
  C.bridge.operatorBody.semiboundedBelowSurface ∧
  C.bridge.operatorBody.eigenWitnessInDomainSurface ∧
  C.bridge.operatorBody.eigenRelationWellTypedSurface ∧
  C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
  C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
  C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
  C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld

/-- Concrete `33/20` closure packet for the `H_phys` operator-body bridge. -/
def exactGap3320HphysOperatorBodyClosure : ExactGapHphysOperatorBodyClosure :=
  { bridge := exactGap3320HphysOperatorBodyBridge
    bridgeReady := exact_gap_3320_hphys_operator_body_bridge_ready
    operatorBodyReady := Hamiltonian.hphys_3320_operator_body_surface_ready
    hamiltonianIsHphys := exactGap3320HphysOperatorBodyBridge.hamiltonianIsHphys
    denseDomainSurface := exactGap3320HphysOperatorBodyBridge.denseDomainSurface
    vacuumInDomainSurface := exactGap3320HphysOperatorBodyBridge.vacuumInDomainSurface
    orthogonalSectorAdmissibleSurface := exactGap3320HphysOperatorBodyBridge.orthogonalSectorAdmissibleSurface
    selfAdjointSurface := exactGap3320HphysOperatorBodyBridge.selfAdjointSurface
    semiboundedBelowSurface := exactGap3320HphysOperatorBodyBridge.semiboundedBelowSurface
    eigenWitnessInDomainSurface := exactGap3320HphysOperatorBodyBridge.eigenWitnessInDomainSurface
    eigenRelationWellTypedSurface := exactGap3320HphysOperatorBodyBridge.eigenRelationWellTypedSurface
    exactGapValue3320 := exact_gap_3320_hphys_operator_body_bridge_value
    finalReleaseHeld := exact_gap_3320_hphys_operator_body_bridge_release_held
    publicBoundaryLocked := exact_gap_3320_hphys_operator_body_bridge_public_boundary_locked
    noAutoRelease := exact_gap_3320_hphys_operator_body_bridge_no_auto_release
    theoremBoundaryHeld := exactGap3320HphysOperatorBodyBridge.theoremBoundaryHeld }

theorem exact_gap_hphys_operator_body_closure_pack
    (C : ExactGapHphysOperatorBodyClosure) :
    C.ready ↔ C.bridge.ready ∧ C.bridge.operatorBody.ready ∧
      C.bridge.operatorBody.hamiltonian = Hamiltonian.Hphys ∧
      C.bridge.operatorBody.denseDomainSurface ∧
      C.bridge.operatorBody.vacuumInDomainSurface ∧
      C.bridge.operatorBody.orthogonalSectorAdmissibleSurface ∧
      C.bridge.operatorBody.selfAdjointSurface ∧
      C.bridge.operatorBody.semiboundedBelowSurface ∧
      C.bridge.operatorBody.eigenWitnessInDomainSurface ∧
      C.bridge.operatorBody.eigenRelationWellTypedSurface ∧
      C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
      C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
      C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
      C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
      C.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld := by
  rfl

theorem exact_gap_3320_hphys_operator_body_closure_ready :
    exactGap3320HphysOperatorBodyClosure.ready := by
  exact And.intro exactGap3320HphysOperatorBodyClosure.bridgeReady <|
    And.intro exactGap3320HphysOperatorBodyClosure.operatorBodyReady <|
    And.intro exactGap3320HphysOperatorBodyClosure.hamiltonianIsHphys <|
    And.intro exactGap3320HphysOperatorBodyClosure.denseDomainSurface <|
    And.intro exactGap3320HphysOperatorBodyClosure.vacuumInDomainSurface <|
    And.intro exactGap3320HphysOperatorBodyClosure.orthogonalSectorAdmissibleSurface <|
    And.intro exactGap3320HphysOperatorBodyClosure.selfAdjointSurface <|
    And.intro exactGap3320HphysOperatorBodyClosure.semiboundedBelowSurface <|
    And.intro exactGap3320HphysOperatorBodyClosure.eigenWitnessInDomainSurface <|
    And.intro exactGap3320HphysOperatorBodyClosure.eigenRelationWellTypedSurface <|
    And.intro exactGap3320HphysOperatorBodyClosure.exactGapValue3320 <|
    And.intro exactGap3320HphysOperatorBodyClosure.finalReleaseHeld <|
    And.intro exactGap3320HphysOperatorBodyClosure.publicBoundaryLocked <|
    And.intro exactGap3320HphysOperatorBodyClosure.noAutoRelease
      exactGap3320HphysOperatorBodyClosure.theoremBoundaryHeld

theorem exact_gap_3320_hphys_operator_body_closure_value :
    exactGap3320HphysOperatorBodyClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 := by
  exact exactGap3320HphysOperatorBodyClosure.exactGapValue3320

theorem exact_gap_3320_hphys_operator_body_closure_release_held :
    exactGap3320HphysOperatorBodyClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld := by
  exact exactGap3320HphysOperatorBodyClosure.finalReleaseHeld

theorem exact_gap_3320_hphys_operator_body_closure_public_boundary_locked :
    exactGap3320HphysOperatorBodyClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked := by
  exact exactGap3320HphysOperatorBodyClosure.publicBoundaryLocked

theorem exact_gap_3320_hphys_operator_body_closure_no_auto_release :
    exactGap3320HphysOperatorBodyClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease := by
  exact exactGap3320HphysOperatorBodyClosure.noAutoRelease

theorem exact_gap_3320_hphys_operator_body_closure_self_adjoint_surface :
    exactGap3320HphysOperatorBodyClosure.bridge.operatorBody.selfAdjointSurface := by
  exact exactGap3320HphysOperatorBodyClosure.selfAdjointSurface

theorem exact_gap_3320_hphys_operator_body_closure_semibounded_surface :
    exactGap3320HphysOperatorBodyClosure.bridge.operatorBody.semiboundedBelowSurface := by
  exact exactGap3320HphysOperatorBodyClosure.semiboundedBelowSurface

end MGAP4D
