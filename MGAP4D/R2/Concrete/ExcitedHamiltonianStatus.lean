import MGAP4D.R2.Concrete.SelfAdjointRestrictionStatus

namespace MGAP4D
namespace R2
namespace Concrete

structure ExcitedHamiltonianStatus where
  selfAdjointRestrictionReady : Prop
  excitedHamiltonianDeclared : Prop
  nonnegativeTargetRecorded : Prop
  quadraticFormLinkRecorded : Prop
  exportToR4Deferred : Prop

def ExcitedHamiltonianStatus.ready (S : ExcitedHamiltonianStatus) : Prop :=
  S.selfAdjointRestrictionReady ∧ S.excitedHamiltonianDeclared ∧
  S.nonnegativeTargetRecorded ∧ S.quadraticFormLinkRecorded ∧ S.exportToR4Deferred

theorem excited_hamiltonian_status_pack
    (S : ExcitedHamiltonianStatus) :
    S.ready ↔ S.selfAdjointRestrictionReady ∧ S.excitedHamiltonianDeclared ∧
      S.nonnegativeTargetRecorded ∧ S.quadraticFormLinkRecorded ∧ S.exportToR4Deferred := by
  rfl

end Concrete
end R2
end MGAP4D
