import MGAP4D.MathlibAdoptionGate.DryRunBranchPlan
import MGAP4D.ReplacementPass2Closure

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunGate where
  pass2Closed : Prop
  preMathlibGateReady : Prop
  mathlibGateReady : Prop
  dryRunPlanReady : Prop
  mainBranchProtected : Prop
  publicBoundaryHeld : Prop

def DryRunGate.ready (G : DryRunGate) : Prop :=
  G.pass2Closed ∧ G.preMathlibGateReady ∧ G.mathlibGateReady ∧
  G.dryRunPlanReady ∧ G.mainBranchProtected ∧ G.publicBoundaryHeld

theorem dry_run_gate_pack
    (G : DryRunGate) :
    G.ready ↔ G.pass2Closed ∧ G.preMathlibGateReady ∧ G.mathlibGateReady ∧
      G.dryRunPlanReady ∧ G.mainBranchProtected ∧ G.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
