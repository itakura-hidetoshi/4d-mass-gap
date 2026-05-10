import MGAP4D.OperatorAPI.TheoremSurface.ExecutionSurface

namespace MGAP4D
namespace OperatorAPI
namespace TheoremSurface

structure ReviewGateSurface where
  executionSurfaceReady : Prop
  publicClaimReviewGated : Prop
  independentReplayRequired : Prop
  externalAuditRequired : Prop
  theoremSurfaceNotFinalClaim : Prop

def ReviewGateSurface.ready (S : ReviewGateSurface) : Prop :=
  S.executionSurfaceReady ∧ S.publicClaimReviewGated ∧ S.independentReplayRequired ∧
  S.externalAuditRequired ∧ S.theoremSurfaceNotFinalClaim

theorem review_gate_surface_pack
    (S : ReviewGateSurface) :
    S.ready ↔ S.executionSurfaceReady ∧ S.publicClaimReviewGated ∧
      S.independentReplayRequired ∧ S.externalAuditRequired ∧ S.theoremSurfaceNotFinalClaim := by
  rfl

structure OperatorAPITheoremSurface where
  candidate : CandidateRegistrySurface
  dependency : DependencySurface
  execution : ExecutionSurface
  review : ReviewGateSurface

def OperatorAPITheoremSurface.ready (S : OperatorAPITheoremSurface) : Prop :=
  S.candidate.ready ∧ S.dependency.ready ∧ S.execution.ready ∧ S.review.ready

theorem operator_api_theorem_surface_pack
    (S : OperatorAPITheoremSurface) :
    S.ready ↔ S.candidate.ready ∧ S.dependency.ready ∧ S.execution.ready ∧ S.review.ready := by
  rfl

end TheoremSurface
end OperatorAPI
end MGAP4D
