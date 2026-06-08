import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR1ResidualPlanBridge
import MGAP4D.Hamiltonian.OperatorBody

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Bridge from the concrete R1 Hilbert substrate/residual-plan bridge to the
`H_phys` operator-body surface.

This is still a surface-level bridge.  It confirms that the Mathlib-grounded R1
carrier can be read alongside the current `H_phys` operator-body obligations,
without upgrading those obligations to completed self-adjointness, spectral
measure, PVM, exact atom derivation, or positive spectral-weight theorems. -/
structure ConcreteR1HphysOperatorBodyBridge where
  r1ResidualBridge : ConcreteR1ResidualPlanBridge
  r1ResidualBridgeReady : r1ResidualBridge.ready
  operatorBody : Hamiltonian.HphysOperatorBodySurface
  operatorBodyReady : operatorBody.ready
  r1BoundaryHeld : concreteR1HardeningResidualBoundaryHeld
  residualBridgeNoAutoRelease :
    r1ResidualBridge.residualPlan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease
  operatorBodyNoAutoRelease :
    operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease
  operatorBodyExactGapValue3320 :
    operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20
  operatorBodyReleaseHeld :
    operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld
  operatorBodyPublicBoundaryLocked :
    operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked
  denseDomainSurfaceVisible : operatorBody.denseDomainSurface
  eigenRelationSurfaceVisible : operatorBody.eigenRelationWellTypedSurface
  bridgeVisible : Prop
  boundaryBeforeSpectralPromotion : Prop

/-- Readiness predicate for the R1-to-`H_phys` operator-body bridge. -/
def ConcreteR1HphysOperatorBodyBridge.ready
    (B : ConcreteR1HphysOperatorBodyBridge) : Prop :=
  B.r1ResidualBridge.ready ∧
  B.operatorBody.ready ∧
  concreteR1HardeningResidualBoundaryHeld ∧
  B.r1ResidualBridge.residualPlan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
  B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
  B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
  B.operatorBody.denseDomainSurface ∧
  B.operatorBody.eigenRelationWellTypedSurface ∧
  B.bridgeVisible ∧
  B.boundaryBeforeSpectralPromotion

/-- The concrete R1-to-`H_phys` operator-body bridge for the `33/20` spine. -/
def concreteR1HphysOperatorBodyBridge3320 : ConcreteR1HphysOperatorBodyBridge :=
  { r1ResidualBridge := concreteR1ResidualPlanBridge3320
    r1ResidualBridgeReady := concrete_r1_residual_plan_bridge_3320_ready
    operatorBody := Hamiltonian.hphys3320OperatorBodySurface
    operatorBodyReady := Hamiltonian.hphys_3320_operator_body_surface_ready
    r1BoundaryHeld := concrete_r1_hardening_residual_boundary_held
    residualBridgeNoAutoRelease := concrete_r1_residual_plan_bridge_no_auto_release
    operatorBodyNoAutoRelease := Hamiltonian.hphys_3320_operator_body_no_auto_release
    operatorBodyExactGapValue3320 := Hamiltonian.hphys_3320_operator_body_exact_gap_value
    operatorBodyReleaseHeld := Hamiltonian.hphys_3320_operator_body_release_held
    operatorBodyPublicBoundaryLocked := Hamiltonian.hphys_3320_operator_body_public_boundary_locked
    denseDomainSurfaceVisible := Hamiltonian.hphys_3320_dense_domain_surface
    eigenRelationSurfaceVisible := Hamiltonian.hphys_3320_eigen_relation_well_typed_surface
    bridgeVisible := True
    boundaryBeforeSpectralPromotion := True }

/-- Expanded view of the R1-to-`H_phys` operator-body bridge readiness predicate. -/
theorem concrete_r1_hphys_operator_body_bridge_pack
    (B : ConcreteR1HphysOperatorBodyBridge) :
    B.ready ↔
      B.r1ResidualBridge.ready ∧
      B.operatorBody.ready ∧
      concreteR1HardeningResidualBoundaryHeld ∧
      B.r1ResidualBridge.residualPlan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
      B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
      B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
      B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
      B.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
      B.operatorBody.denseDomainSurface ∧
      B.operatorBody.eigenRelationWellTypedSurface ∧
      B.bridgeVisible ∧
      B.boundaryBeforeSpectralPromotion := by
  rfl

/-- The concrete R1-to-`H_phys` operator-body bridge is ready. -/
theorem concrete_r1_hphys_operator_body_bridge_3320_ready :
    concreteR1HphysOperatorBodyBridge3320.ready := by
  exact And.intro concreteR1HphysOperatorBodyBridge3320.r1ResidualBridgeReady <|
    And.intro concreteR1HphysOperatorBodyBridge3320.operatorBodyReady <|
    And.intro concrete_r1_hardening_residual_boundary_held <|
    And.intro concreteR1HphysOperatorBodyBridge3320.residualBridgeNoAutoRelease <|
    And.intro concreteR1HphysOperatorBodyBridge3320.operatorBodyNoAutoRelease <|
    And.intro concreteR1HphysOperatorBodyBridge3320.operatorBodyExactGapValue3320 <|
    And.intro concreteR1HphysOperatorBodyBridge3320.operatorBodyReleaseHeld <|
    And.intro concreteR1HphysOperatorBodyBridge3320.operatorBodyPublicBoundaryLocked <|
    And.intro concreteR1HphysOperatorBodyBridge3320.denseDomainSurfaceVisible <|
    And.intro concreteR1HphysOperatorBodyBridge3320.eigenRelationSurfaceVisible <|
    And.intro True.intro True.intro

/-- Projection: adding the concrete R1 bridge does not open the final-release gate
through the `H_phys` operator-body surface. -/
theorem concrete_r1_hphys_operator_body_bridge_no_auto_release :
    concreteR1HphysOperatorBodyBridge3320.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease := by
  exact concreteR1HphysOperatorBodyBridge3320.operatorBodyNoAutoRelease

/-- Projection: the bridge keeps the `33/20` value reading tied to the existing
operator-body surface. -/
theorem concrete_r1_hphys_operator_body_bridge_3320_value :
    concreteR1HphysOperatorBodyBridge3320.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 := by
  exact concreteR1HphysOperatorBodyBridge3320.operatorBodyExactGapValue3320

end

end MathlibAnalytic
end MGAP4D
