namespace MGAP4D
namespace Global
namespace Concrete

structure WUR3UnboundedKernelGlobalAuditStatus where
  selected_after_r4 : Prop
  uses_shifted_nonnegative_route : Prop
  produces_kernel_step : Prop
  no_release_effect : Prop
  audit_required : Prop

def WUR3UnboundedKernelGlobalAuditStatus.ready (S : WUR3UnboundedKernelGlobalAuditStatus) : Prop :=
  S.selected_after_r4 ∧ S.uses_shifted_nonnegative_route ∧
  S.produces_kernel_step ∧ S.no_release_effect ∧ S.audit_required

theorem wu_r3_unbounded_kernel_global_audit_status_pack
    (S : WUR3UnboundedKernelGlobalAuditStatus) :
    S.ready ↔ S.selected_after_r4 ∧ S.uses_shifted_nonnegative_route ∧
      S.produces_kernel_step ∧ S.no_release_effect ∧ S.audit_required := by
  rfl

end Concrete
end Global
end MGAP4D
