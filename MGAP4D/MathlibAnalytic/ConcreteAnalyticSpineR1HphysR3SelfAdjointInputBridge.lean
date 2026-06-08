import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR1HphysOperatorBodyBridge
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Bridge from the concrete R1/`H_phys` operator-body surface to the existing
hard-residual R3 self-adjointness theorem-input bundle.

This is deliberately a theorem-input bridge, not a self-adjointness theorem.  It
keeps the Mathlib-grounded Hilbert substrate, the `H_phys` operator-body surface,
and the graph-level R3 inputs visible together, while preserving the existing
non-promotion boundary. -/
structure ConcreteR1HphysR3SelfAdjointInputBridge where
  r1HphysBridge : ConcreteR1HphysOperatorBodyBridge
  r1HphysBridgeReady : r1HphysBridge.ready
  r3InputsClosed : concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed
  r3PreInputReady : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput
  r3GraphEqualityBundle : concreteAnalyticSpineHardResidualR3GraphEqualityInputBundle
  formalGraphSelfAdjointness : concreteL2R4FormalGraphSelfAdjointness
  nonPromotionBoundary : concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness
  r1HphysNoAutoRelease :
    r1HphysBridge.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease
  r1HphysExactGapValue3320 :
    r1HphysBridge.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20
  bridgeVisible : Prop
  boundaryBeforeSelfAdjointPromotion : Prop

/-- Readiness predicate for the R1/`H_phys` to R3 theorem-input bridge. -/
def ConcreteR1HphysR3SelfAdjointInputBridge.ready
    (B : ConcreteR1HphysR3SelfAdjointInputBridge) : Prop :=
  B.r1HphysBridge.ready ∧
  concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed ∧
  concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput ∧
  concreteAnalyticSpineHardResidualR3GraphEqualityInputBundle ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  B.r1HphysBridge.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  B.r1HphysBridge.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
  B.bridgeVisible ∧
  B.boundaryBeforeSelfAdjointPromotion

/-- The concrete R1/`H_phys` to R3 self-adjointness theorem-input bridge. -/
def concreteR1HphysR3SelfAdjointInputBridge3320 :
    ConcreteR1HphysR3SelfAdjointInputBridge :=
  { r1HphysBridge := concreteR1HphysOperatorBodyBridge3320
    r1HphysBridgeReady := concrete_r1_hphys_operator_body_bridge_3320_ready
    r3InputsClosed :=
      concrete_analytic_spine_hard_residual_r3_self_adjoint_theorem_inputs_closed_ready
    r3PreInputReady :=
      concrete_analytic_spine_hard_residual_r3_concrete_self_adjoint_theorem_preinput_ready
    r3GraphEqualityBundle :=
      concrete_analytic_spine_hard_residual_r3_graph_equality_input_bundle_ready
    formalGraphSelfAdjointness :=
      concrete_analytic_spine_hard_residual_r3_has_formal_graph_self_adjointness
    nonPromotionBoundary :=
      concrete_l2_r2_closed_operator_boundary_not_self_adjointness
    r1HphysNoAutoRelease :=
      concrete_r1_hphys_operator_body_bridge_no_auto_release
    r1HphysExactGapValue3320 :=
      concrete_r1_hphys_operator_body_bridge_3320_value
    bridgeVisible := True
    boundaryBeforeSelfAdjointPromotion := True }

/-- Expanded view of the R1/`H_phys` to R3 theorem-input bridge. -/
theorem concrete_r1_hphys_r3_self_adjoint_input_bridge_pack
    (B : ConcreteR1HphysR3SelfAdjointInputBridge) :
    B.ready ↔
      B.r1HphysBridge.ready ∧
      concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed ∧
      concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput ∧
      concreteAnalyticSpineHardResidualR3GraphEqualityInputBundle ∧
      concreteL2R4FormalGraphSelfAdjointness ∧
      concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
      B.r1HphysBridge.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
      B.r1HphysBridge.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
      B.bridgeVisible ∧
      B.boundaryBeforeSelfAdjointPromotion := by
  rfl

/-- The concrete R1/`H_phys` to R3 theorem-input bridge is ready. -/
theorem concrete_r1_hphys_r3_self_adjoint_input_bridge_3320_ready :
    concreteR1HphysR3SelfAdjointInputBridge3320.ready := by
  exact And.intro concreteR1HphysR3SelfAdjointInputBridge3320.r1HphysBridgeReady <|
    And.intro concreteR1HphysR3SelfAdjointInputBridge3320.r3InputsClosed <|
    And.intro concreteR1HphysR3SelfAdjointInputBridge3320.r3PreInputReady <|
    And.intro concreteR1HphysR3SelfAdjointInputBridge3320.r3GraphEqualityBundle <|
    And.intro concreteR1HphysR3SelfAdjointInputBridge3320.formalGraphSelfAdjointness <|
    And.intro concreteR1HphysR3SelfAdjointInputBridge3320.nonPromotionBoundary <|
    And.intro concreteR1HphysR3SelfAdjointInputBridge3320.r1HphysNoAutoRelease <|
    And.intro concreteR1HphysR3SelfAdjointInputBridge3320.r1HphysExactGapValue3320 <|
    And.intro True.intro True.intro

/-- Projection: the R3 bridge exposes the formal graph self-adjointness input only
as a theorem-input surface. -/
theorem concrete_r1_hphys_r3_self_adjoint_input_bridge_formal_graph :
    concreteL2R4FormalGraphSelfAdjointness := by
  exact concreteR1HphysR3SelfAdjointInputBridge3320.formalGraphSelfAdjointness

/-- Projection: the R3 bridge still carries the non-promotion boundary. -/
theorem concrete_r1_hphys_r3_self_adjoint_input_bridge_nonpromotion_boundary :
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  exact concreteR1HphysR3SelfAdjointInputBridge3320.nonPromotionBoundary

/-- Projection: the R1/`H_phys` side still does not open final release. -/
theorem concrete_r1_hphys_r3_self_adjoint_input_bridge_no_auto_release :
    concreteR1HphysR3SelfAdjointInputBridge3320.r1HphysBridge.operatorBody.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease := by
  exact concreteR1HphysR3SelfAdjointInputBridge3320.r1HphysNoAutoRelease

end

end MathlibAnalytic
end MGAP4D
