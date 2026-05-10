namespace MGAP4D
namespace Global
namespace Concrete

structure WUGlobalFinalAuditStatus where
  terminal_selected : Prop
  previous_units_collected : Prop
  gates_layered : Prop
  replay_required : Prop
  review_required : Prop

def WUGlobalFinalAuditStatus.ready (S : WUGlobalFinalAuditStatus) : Prop :=
  S.terminal_selected ∧ S.previous_units_collected ∧ S.gates_layered ∧ S.replay_required ∧ S.review_required

theorem wu_global_final_audit_status_pack
    (S : WUGlobalFinalAuditStatus) :
    S.ready ↔ S.terminal_selected ∧ S.previous_units_collected ∧ S.gates_layered ∧ S.replay_required ∧ S.review_required := by
  rfl

end Concrete
end Global
end MGAP4D
