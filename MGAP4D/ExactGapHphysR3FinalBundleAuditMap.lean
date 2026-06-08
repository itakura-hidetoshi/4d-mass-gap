import MGAP4D.ExactGapHphysR3FinalBundleAuditChainIndex

namespace MGAP4D

/-- A small audit-map layer over the `H_phys`/R3 final-bundle audit chain index.

This is deliberately only a map: it reads the chain-index readiness and exposes the
boundary witnesses that must remain visible.  It does not promote the R3 input
surface into a completed self-adjointness theorem and does not open final release. -/
structure ExactGapHphysR3FinalBundleAuditMap where
  chainIndexReady : ExactGapHphysR3FinalBundleAuditChainIndexReady
  targetsListed :
    exactGapHphysR3FinalBundleAuditChainTargets =
      exactGapHphysR3FinalBundleAuditChainTargets
  r3InputsClosed :
    MathlibAnalytic.concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed
  nonPromotionBoundary :
    MathlibAnalytic.concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness
  noAutoRelease :
    exactGap3320HphysToFinalTheoremReleaseBundleHandoff.hphysToFinal.hphysToOrigin.hphysClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease
  publicBoundaryHeld :
    MathlibAnalytic.prototypeFinalTheoremReleaseBundleManifestData.publicBoundaryHeld
  mapVisible : Prop

/-- Readiness predicate for the audit map.

The left-hand entries are the propositions witnessed by the map fields.  They are
written as propositions rather than as field projections, because the projections
are proof terms. -/
def ExactGapHphysR3FinalBundleAuditMap.ready
    (M : ExactGapHphysR3FinalBundleAuditMap) : Prop :=
  ExactGapHphysR3FinalBundleAuditChainIndexReady ∧
  exactGapHphysR3FinalBundleAuditChainTargets =
    exactGapHphysR3FinalBundleAuditChainTargets ∧
  MathlibAnalytic.concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed ∧
  MathlibAnalytic.concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  exactGap3320HphysToFinalTheoremReleaseBundleHandoff.hphysToFinal.hphysToOrigin.hphysClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  MathlibAnalytic.prototypeFinalTheoremReleaseBundleManifestData.publicBoundaryHeld ∧
  M.mapVisible

/-- Canonical audit map for the `H_phys`/R3 final-bundle audit chain. -/
def exactGapHphysR3FinalBundleAuditMap3320 :
    ExactGapHphysR3FinalBundleAuditMap :=
  { chainIndexReady := exact_gap_hphys_r3_final_bundle_audit_chain_index_ready
    targetsListed := rfl
    r3InputsClosed :=
      exact_gap_hphys_r3_final_bundle_audit_chain_index_r3_inputs_closed
    nonPromotionBoundary :=
      exact_gap_hphys_r3_final_bundle_audit_chain_index_nonpromotion_boundary
    noAutoRelease :=
      exact_gap_hphys_r3_final_bundle_audit_chain_index_no_auto_release
    publicBoundaryHeld :=
      exact_gap_3320_hphys_to_final_theorem_release_bundle_public_boundary_held
    mapVisible := True }

/-- The canonical audit map is ready. -/
theorem exact_gap_hphys_r3_final_bundle_audit_map_3320_ready :
    exactGapHphysR3FinalBundleAuditMap3320.ready := by
  exact ⟨
    exactGapHphysR3FinalBundleAuditMap3320.chainIndexReady,
    exactGapHphysR3FinalBundleAuditMap3320.targetsListed,
    exactGapHphysR3FinalBundleAuditMap3320.r3InputsClosed,
    exactGapHphysR3FinalBundleAuditMap3320.nonPromotionBoundary,
    exactGapHphysR3FinalBundleAuditMap3320.noAutoRelease,
    exactGapHphysR3FinalBundleAuditMap3320.publicBoundaryHeld,
    True.intro⟩

/-- Projection: the audit map keeps the chain index ready. -/
theorem exact_gap_hphys_r3_final_bundle_audit_map_chain_index_ready :
    ExactGapHphysR3FinalBundleAuditChainIndexReady := by
  exact exactGapHphysR3FinalBundleAuditMap3320.chainIndexReady

/-- Projection: the audit map keeps no-auto-release visible. -/
theorem exact_gap_hphys_r3_final_bundle_audit_map_no_auto_release :
    exactGap3320HphysToFinalTheoremReleaseBundleHandoff.hphysToFinal.hphysToOrigin.hphysClosure.bridge.structuralSurface.plan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease := by
  exact exactGapHphysR3FinalBundleAuditMap3320.noAutoRelease

/-- Projection: the audit map keeps the non-promotion boundary visible. -/
theorem exact_gap_hphys_r3_final_bundle_audit_map_nonpromotion_boundary :
    MathlibAnalytic.concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  exact exactGapHphysR3FinalBundleAuditMap3320.nonPromotionBoundary

end MGAP4D
