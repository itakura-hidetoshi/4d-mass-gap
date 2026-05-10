import MGAP4D.ProofHardening.Plan

namespace MGAP4D
namespace ProofHardening

structure HardeningGate where
  sourceBatchBuilds : Prop
  auditPasses : Prop
  deferredImportsRecorded : Prop
  theoremSurfaceSmallEnough : Prop
  reviewGateActive : Prop

def HardeningGate.ready (G : HardeningGate) : Prop :=
  G.sourceBatchBuilds ∧ G.auditPasses ∧ G.deferredImportsRecorded ∧
  G.theoremSurfaceSmallEnough ∧ G.reviewGateActive

theorem hardening_gate_pack
    (G : HardeningGate) :
    G.ready ↔ G.sourceBatchBuilds ∧ G.auditPasses ∧ G.deferredImportsRecorded ∧
      G.theoremSurfaceSmallEnough ∧ G.reviewGateActive := by
  rfl

end ProofHardening
end MGAP4D
