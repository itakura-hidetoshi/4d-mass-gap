import MGAP4D.R4.Theorem.LowerBoundClosureCandidate

namespace MGAP4D
namespace R4
namespace Theorem

structure LowerBoundHardeningPass where
  closureCandidateVisible : Prop
  lowerBoundRouteSurfaceVisible : Prop
  lowerBoundObligationsVisible : Prop
  upstreamDependencyVisible : Prop
  downstreamR5R7ReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  theoremCompletionNotClaimed : Prop
  publicBoundaryHeld : Prop

def LowerBoundHardeningPass.ready (P : LowerBoundHardeningPass) : Prop :=
  P.closureCandidateVisible ∧ P.lowerBoundRouteSurfaceVisible ∧
  P.lowerBoundObligationsVisible ∧ P.upstreamDependencyVisible ∧
  P.downstreamR5R7ReviewGated ∧ P.mathlibDryRunNotCompletion ∧
  P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld

theorem lower_bound_hardening_pass_pack (P : LowerBoundHardeningPass) :
    P.ready ↔ P.closureCandidateVisible ∧ P.lowerBoundRouteSurfaceVisible ∧
      P.lowerBoundObligationsVisible ∧ P.upstreamDependencyVisible ∧
      P.downstreamR5R7ReviewGated ∧ P.mathlibDryRunNotCompletion ∧
      P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
