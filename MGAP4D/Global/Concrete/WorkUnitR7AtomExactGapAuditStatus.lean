namespace MGAP4D
namespace Global
namespace Concrete

structure WUR7AtomExactGapGlobalAuditStatus where
  selected_after_r3 : Prop
  uses_atom_persistence : Prop
  produces_exact_gap_surface : Prop
  no_release_effect : Prop
  audit_required : Prop

def WUR7AtomExactGapGlobalAuditStatus.ready (S : WUR7AtomExactGapGlobalAuditStatus) : Prop :=
  S.selected_after_r3 ∧ S.uses_atom_persistence ∧
  S.produces_exact_gap_surface ∧ S.no_release_effect ∧ S.audit_required

theorem wu_r7_atom_exact_gap_global_audit_status_pack
    (S : WUR7AtomExactGapGlobalAuditStatus) :
    S.ready ↔ S.selected_after_r3 ∧ S.uses_atom_persistence ∧
      S.produces_exact_gap_surface ∧ S.no_release_effect ∧ S.audit_required := by
  rfl

end Concrete
end Global
end MGAP4D
