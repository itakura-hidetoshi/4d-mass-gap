namespace MGAP4D
namespace Global
namespace Concrete

structure WUR1ProjectionGlobalAuditStatus where
  selected_after_ell : Prop
  unlocks_r2_path : Prop
  no_release_effect : Prop
  audit_required : Prop

def WUR1ProjectionGlobalAuditStatus.ready (S : WUR1ProjectionGlobalAuditStatus) : Prop :=
  S.selected_after_ell ∧ S.unlocks_r2_path ∧ S.no_release_effect ∧ S.audit_required

theorem wu_r1_projection_global_audit_status_pack
    (S : WUR1ProjectionGlobalAuditStatus) :
    S.ready ↔ S.selected_after_ell ∧ S.unlocks_r2_path ∧ S.no_release_effect ∧ S.audit_required := by
  rfl

end Concrete
end Global
end MGAP4D
