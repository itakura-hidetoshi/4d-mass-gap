namespace MGAP4D
namespace Global
namespace Concrete

structure WUR4LowerBoundGlobalAuditStatus where
  analytic_core : Prop
  unlocks_r3 : Prop
  unlocks_r5 : Prop
  no_release_effect : Prop
  audit_required : Prop

def WUR4LowerBoundGlobalAuditStatus.ready (S : WUR4LowerBoundGlobalAuditStatus) : Prop :=
  S.analytic_core ∧ S.unlocks_r3 ∧ S.unlocks_r5 ∧ S.no_release_effect ∧ S.audit_required

theorem wu_r4_lower_bound_global_audit_status_pack
    (S : WUR4LowerBoundGlobalAuditStatus) :
    S.ready ↔ S.analytic_core ∧ S.unlocks_r3 ∧ S.unlocks_r5 ∧ S.no_release_effect ∧ S.audit_required := by
  rfl

end Concrete
end Global
end MGAP4D
