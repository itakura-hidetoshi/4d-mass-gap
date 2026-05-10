import MGAP4D.OperatorAPI.BindingObligations

namespace MGAP4D
namespace OperatorAPI

structure AdoptionPlan where
  candidateRegistryReady : Prop
  bindingObligationsReady : Prop
  stagedMigration : Prop
  deferredImportsRecorded : Prop
  ciGreenRequired : Prop

def AdoptionPlan.ready (A : AdoptionPlan) : Prop :=
  A.candidateRegistryReady ∧ A.bindingObligationsReady ∧
  A.stagedMigration ∧ A.deferredImportsRecorded ∧ A.ciGreenRequired

theorem adoption_plan_pack
    (A : AdoptionPlan) :
    A.ready ↔ A.candidateRegistryReady ∧ A.bindingObligationsReady ∧
      A.stagedMigration ∧ A.deferredImportsRecorded ∧ A.ciGreenRequired := by
  rfl

end OperatorAPI
end MGAP4D
