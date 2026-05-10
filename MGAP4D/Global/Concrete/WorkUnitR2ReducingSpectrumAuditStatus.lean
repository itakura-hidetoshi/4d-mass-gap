namespace MGAP4D
namespace Global
namespace Concrete

structure WUR2ReducingSpectrumGlobalAuditStatus where
  selected_after_r1_projection : Prop
  produces_reducing_layer : Prop
  produces_spectrum_union_surface : Prop
  no_release_effect : Prop
  audit_required : Prop

def WUR2ReducingSpectrumGlobalAuditStatus.ready (S : WUR2ReducingSpectrumGlobalAuditStatus) : Prop :=
  S.selected_after_r1_projection ∧ S.produces_reducing_layer ∧
  S.produces_spectrum_union_surface ∧ S.no_release_effect ∧ S.audit_required

theorem wu_r2_reducing_spectrum_global_audit_status_pack
    (S : WUR2ReducingSpectrumGlobalAuditStatus) :
    S.ready ↔ S.selected_after_r1_projection ∧ S.produces_reducing_layer ∧
      S.produces_spectrum_union_surface ∧ S.no_release_effect ∧ S.audit_required := by
  rfl

end Concrete
end Global
end MGAP4D
