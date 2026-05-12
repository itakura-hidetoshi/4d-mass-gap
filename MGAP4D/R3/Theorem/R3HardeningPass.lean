import MGAP4D.R3.Theorem.R3ClosureCandidate

namespace MGAP4D
namespace R3
namespace Theorem

structure R3HardeningPass where
  closureCandidateVisible : Prop
  shiftedRouteSurfaceVisible : Prop
  zeroFormRouteSurfaceVisible : Prop
  operatorBoundaryVisible : Prop
  proofObligationsVisible : Prop
  downstreamR4R7ReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  theoremCompletionNotClaimed : Prop
  publicBoundaryHeld : Prop

def R3HardeningPass.ready (P : R3HardeningPass) : Prop :=
  P.closureCandidateVisible ∧ P.shiftedRouteSurfaceVisible ∧
  P.zeroFormRouteSurfaceVisible ∧ P.operatorBoundaryVisible ∧
  P.proofObligationsVisible ∧ P.downstreamR4R7ReviewGated ∧
  P.mathlibDryRunNotCompletion ∧ P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld

theorem r3_hardening_pass_pack (P : R3HardeningPass) :
    P.ready ↔ P.closureCandidateVisible ∧ P.shiftedRouteSurfaceVisible ∧
      P.zeroFormRouteSurfaceVisible ∧ P.operatorBoundaryVisible ∧
      P.proofObligationsVisible ∧ P.downstreamR4R7ReviewGated ∧
      P.mathlibDryRunNotCompletion ∧ P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R3
end MGAP4D
