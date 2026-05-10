namespace MGAP4D
namespace Global
namespace Concrete

structure RootManifestStatus where
  manifest_present : Prop
  summary_present : Prop
  digest_recorded : Prop
  gate_active : Prop

def RootManifestStatus.ready (S : RootManifestStatus) : Prop :=
  S.manifest_present ∧ S.summary_present ∧ S.digest_recorded ∧ S.gate_active

theorem root_manifest_status_pack
    (S : RootManifestStatus) :
    S.ready ↔
      S.manifest_present ∧ S.summary_present ∧ S.digest_recorded ∧ S.gate_active := by
  rfl

end Concrete
end Global
end MGAP4D
