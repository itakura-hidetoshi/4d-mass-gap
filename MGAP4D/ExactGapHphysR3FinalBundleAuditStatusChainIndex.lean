import MGAP4D.ExactGapHphysR3FinalBundleAuditStatus

namespace MGAP4D

/-- Chain-index targets for the `H_phys`/R3 final-bundle audit status layer.

This is a navigation surface over the status layer.  It keeps the map readiness and
boundary guards visible without promoting the R3 input surface into a completed
self-adjointness theorem and without opening final release. -/
inductive ExactGapHphysR3FinalBundleAuditStatusChainTarget where
  | auditStatus
  | auditMapReady
  | nonPromotionBoundary
  | noAutoRelease
  | publicBoundaryHeld
  deriving Repr, DecidableEq

/-- Ordered visible targets for the `H_phys`/R3 final-bundle audit status layer. -/
def exactGapHphysR3FinalBundleAuditStatusChainTargets :
    List ExactGapHphysR3FinalBundleAuditStatusChainTarget :=
  [ ExactGapHphysR3FinalBundleAuditStatusChainTarget.auditStatus
  , ExactGapHphysR3FinalBundleAuditStatusChainTarget.auditMapReady
  , ExactGapHphysR3FinalBundleAuditStatusChainTarget.nonPromotionBoundary
  , ExactGapHphysR3FinalBundleAuditStatusChainTarget.noAutoRelease
  , ExactGapHphysR3FinalBundleAuditStatusChainTarget.publicBoundaryHeld ]

/-- Readiness predicate for the status-chain index.

Each conjunct is a proposition, not a proof-field projection.  This avoids treating
proof terms stored inside records as proposition expressions. -/
def ExactGapHphysR3FinalBundleAuditStatusChainIndexReady : Prop :=
  exactGapHphysR3FinalBundleAuditStatus3320.ready ∧
  exactGapHphysR3FinalBundleAuditStatus3320.auditMap.ready ∧
  MathlibAnalytic.concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  exactGap3320HphysToFinalTheoremReleaseBundleHandoff.hphysToFinal.hphysToOrigin.hphysClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  MathlibAnalytic.prototypeFinalTheoremReleaseBundleManifestData.publicBoundaryHeld

/-- The status-chain index is ready. -/
theorem exact_gap_hphys_r3_final_bundle_audit_status_chain_index_ready :
    ExactGapHphysR3FinalBundleAuditStatusChainIndexReady := by
  exact ⟨
    exact_gap_hphys_r3_final_bundle_audit_status_3320_ready,
    exact_gap_hphys_r3_final_bundle_audit_status_map_ready,
    exact_gap_hphys_r3_final_bundle_audit_status_nonpromotion_boundary,
    exact_gap_hphys_r3_final_bundle_audit_status_no_auto_release,
    exact_gap_hphys_r3_final_bundle_audit_status_public_boundary_held⟩

/-- Projection: the status-chain index keeps the status layer ready. -/
theorem exact_gap_hphys_r3_final_bundle_audit_status_chain_index_status_ready :
    exactGapHphysR3FinalBundleAuditStatus3320.ready := by
  exact exact_gap_hphys_r3_final_bundle_audit_status_3320_ready

/-- Projection: the status-chain index keeps the audit map ready. -/
theorem exact_gap_hphys_r3_final_bundle_audit_status_chain_index_map_ready :
    exactGapHphysR3FinalBundleAuditStatus3320.auditMap.ready := by
  exact exact_gap_hphys_r3_final_bundle_audit_status_map_ready

/-- Projection: the status-chain index keeps the non-promotion boundary visible. -/
theorem exact_gap_hphys_r3_final_bundle_audit_status_chain_index_nonpromotion_boundary :
    MathlibAnalytic.concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  exact exact_gap_hphys_r3_final_bundle_audit_status_nonpromotion_boundary

/-- Projection: the status-chain index keeps the no-auto-release guard visible. -/
theorem exact_gap_hphys_r3_final_bundle_audit_status_chain_index_no_auto_release :
    exactGap3320HphysToFinalTheoremReleaseBundleHandoff.hphysToFinal.hphysToOrigin.hphysClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease := by
  exact exact_gap_hphys_r3_final_bundle_audit_status_no_auto_release

/-- Projection: the status-chain index keeps the public boundary held. -/
theorem exact_gap_hphys_r3_final_bundle_audit_status_chain_index_public_boundary_held :
    MathlibAnalytic.prototypeFinalTheoremReleaseBundleManifestData.publicBoundaryHeld := by
  exact exact_gap_hphys_r3_final_bundle_audit_status_public_boundary_held

end MGAP4D
