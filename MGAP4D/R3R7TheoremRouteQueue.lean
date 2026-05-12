import MGAP4D.R3R7ClosureCandidateSeriesReview

namespace MGAP4D

inductive R3R7QueueItem where
  | r3ShiftedZeroForm
  | r4LowerBound
  | r5SpectrumInfimum
  | r6IntervalExclusion
  | r7AtomExact
  deriving Repr, DecidableEq

structure R3R7TheoremRouteQueue where
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  closureCandidateSeriesGreen : Prop
  r3First : Prop
  r4AfterR3 : Prop
  r5AfterR4 : Prop
  r6AfterR5 : Prop
  r7AfterR6 : Prop
  theoremCompletionNotClaimed : Prop
  publicBoundaryHeld : Prop

def R3R7TheoremRouteQueue.ready (Q : R3R7TheoremRouteQueue) : Prop :=
  Q.mainPreMathlib ∧ Q.mathlibMainAdoptionHeld ∧
  Q.closureCandidateSeriesGreen ∧ Q.r3First ∧ Q.r4AfterR3 ∧
  Q.r5AfterR4 ∧ Q.r6AfterR5 ∧ Q.r7AfterR6 ∧
  Q.theoremCompletionNotClaimed ∧ Q.publicBoundaryHeld

theorem r3_r7_theorem_route_queue_pack (Q : R3R7TheoremRouteQueue) :
    Q.ready ↔ Q.mainPreMathlib ∧ Q.mathlibMainAdoptionHeld ∧
      Q.closureCandidateSeriesGreen ∧ Q.r3First ∧ Q.r4AfterR3 ∧
      Q.r5AfterR4 ∧ Q.r6AfterR5 ∧ Q.r7AfterR6 ∧
      Q.theoremCompletionNotClaimed ∧ Q.publicBoundaryHeld := by
  rfl

end MGAP4D
