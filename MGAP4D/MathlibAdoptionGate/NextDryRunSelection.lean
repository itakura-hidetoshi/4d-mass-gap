import MGAP4D.Phase3CIConfirmationClosure
import MGAP4D.MathlibAdoptionGate.R2RestrictionRequest
import MGAP4D.R2.Theorem.RestrictionMilestone

namespace MGAP4D
namespace MathlibAdoptionGate

structure NextDryRunSelection where
  phase3CiConfirmed : Prop
  r1DryRunAlreadyRecorded : Prop
  r2SelectedNext : Prop
  r2MilestoneReady : Prop
  r2RequestReady : Prop
  r3DeferredAfterR2 : Prop
  mainStillPreMathlib : Prop
  publicBoundaryHeld : Prop

def NextDryRunSelection.ready (S : NextDryRunSelection) : Prop :=
  S.phase3CiConfirmed ∧ S.r1DryRunAlreadyRecorded ∧ S.r2SelectedNext ∧
  S.r2MilestoneReady ∧ S.r2RequestReady ∧ S.r3DeferredAfterR2 ∧
  S.mainStillPreMathlib ∧ S.publicBoundaryHeld

theorem next_dry_run_selection_pack
    (S : NextDryRunSelection) :
    S.ready ↔ S.phase3CiConfirmed ∧ S.r1DryRunAlreadyRecorded ∧ S.r2SelectedNext ∧
      S.r2MilestoneReady ∧ S.r2RequestReady ∧ S.r3DeferredAfterR2 ∧
      S.mainStillPreMathlib ∧ S.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
