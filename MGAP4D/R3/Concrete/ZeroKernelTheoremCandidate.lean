import MGAP4D.R3.Concrete.ZeroFormKernelStatus
import MGAP4D.MathlibAdoptionGate.R3ZeroKernelRequest

namespace MGAP4D
namespace R3
namespace Concrete

structure ZeroKernelTheoremCandidate where
  statusReady : Prop
  shiftedCandidate : Prop
  nonnegativeCandidate : Prop
  zeroFormCandidate : Prop
  sqrtRouteCandidate : Prop
  domainBridgeDeferred : Prop
  exportToR7Deferred : Prop
  r3RequestReady : Prop
  mathlibStillDeferred : Prop

def ZeroKernelTheoremCandidate.ready (C : ZeroKernelTheoremCandidate) : Prop :=
  C.statusReady ∧ C.shiftedCandidate ∧ C.nonnegativeCandidate ∧
  C.zeroFormCandidate ∧ C.sqrtRouteCandidate ∧ C.domainBridgeDeferred ∧
  C.exportToR7Deferred ∧ C.r3RequestReady ∧ C.mathlibStillDeferred

theorem zero_kernel_theorem_candidate_pack
    (C : ZeroKernelTheoremCandidate) :
    C.ready ↔ C.statusReady ∧ C.shiftedCandidate ∧ C.nonnegativeCandidate ∧
      C.zeroFormCandidate ∧ C.sqrtRouteCandidate ∧ C.domainBridgeDeferred ∧
      C.exportToR7Deferred ∧ C.r3RequestReady ∧ C.mathlibStillDeferred := by
  rfl

end Concrete
end R3
end MGAP4D
