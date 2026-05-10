import MGAP4D.OperatorAPI.Phase1Targets

namespace MGAP4D
namespace OperatorAPI

structure PhaseSelectionStatus where
  phasePlanReady : Prop
  phase1Selected : Prop
  phase2DeferredUntilPhase1 : Prop
  phase3DeferredUntilPhase2 : Prop
  terminalAuditDeferred : Prop

def PhaseSelectionStatus.ready (S : PhaseSelectionStatus) : Prop :=
  S.phasePlanReady ∧ S.phase1Selected ∧ S.phase2DeferredUntilPhase1 ∧
  S.phase3DeferredUntilPhase2 ∧ S.terminalAuditDeferred

theorem phase_selection_status_pack
    (S : PhaseSelectionStatus) :
    S.ready ↔ S.phasePlanReady ∧ S.phase1Selected ∧ S.phase2DeferredUntilPhase1 ∧
      S.phase3DeferredUntilPhase2 ∧ S.terminalAuditDeferred := by
  rfl

end OperatorAPI
end MGAP4D
