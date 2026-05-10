import MGAP4D.Global.Concrete

namespace MGAP4D
namespace Global
namespace Concrete

structure GlobalConcreteSummarySurface where
  reviewPacketReady : Prop
  rootManifestReady : Prop
  closurePriorityReady : Prop
  closureDecisionReady : Prop
  workUnitAuditsReady : Prop
  finalAuditReady : Prop
  gateActive : Prop

def GlobalConcreteSummarySurface.ready (S : GlobalConcreteSummarySurface) : Prop :=
  S.reviewPacketReady ∧ S.rootManifestReady ∧ S.closurePriorityReady ∧
  S.closureDecisionReady ∧ S.workUnitAuditsReady ∧ S.finalAuditReady ∧ S.gateActive

theorem global_concrete_summary_surface_pack
    (S : GlobalConcreteSummarySurface) :
    S.ready ↔ S.reviewPacketReady ∧ S.rootManifestReady ∧ S.closurePriorityReady ∧
      S.closureDecisionReady ∧ S.workUnitAuditsReady ∧ S.finalAuditReady ∧ S.gateActive := by
  rfl

structure WorkUnitAuditSummarySurface where
  r1EllReady : Prop
  r1ProjectionReady : Prop
  r2Ready : Prop
  r3Ready : Prop
  r4Ready : Prop
  r7Ready : Prop

def WorkUnitAuditSummarySurface.ready (S : WorkUnitAuditSummarySurface) : Prop :=
  S.r1EllReady ∧ S.r1ProjectionReady ∧ S.r2Ready ∧ S.r3Ready ∧ S.r4Ready ∧ S.r7Ready

theorem work_unit_audit_summary_surface_pack
    (S : WorkUnitAuditSummarySurface) :
    S.ready ↔ S.r1EllReady ∧ S.r1ProjectionReady ∧ S.r2Ready ∧ S.r3Ready ∧ S.r4Ready ∧ S.r7Ready := by
  rfl

end Concrete
end Global
end MGAP4D
