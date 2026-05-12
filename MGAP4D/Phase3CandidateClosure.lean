import MGAP4D.R1.Theorem.HilbertMilestone
import MGAP4D.R2.Theorem.RestrictionMilestone
import MGAP4D.R3.Theorem.R3Milestone
import MGAP4D.R4.Theorem.LowerBoundMilestone
import MGAP4D.R5.Theorem.SpectrumMilestone
import MGAP4D.R6.Theorem.IntervalMilestone
import MGAP4D.R7.Theorem.AtomExactMilestone

namespace MGAP4D

structure Phase3CandidateClosure where
  r1MilestoneRecorded : Prop
  r2MilestoneRecorded : Prop
  r3MilestoneRecorded : Prop
  r4MilestoneRecorded : Prop
  r5MilestoneRecorded : Prop
  r6MilestoneRecorded : Prop
  r7MilestoneRecorded : Prop
  r3OmissionCorrected : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def Phase3CandidateClosure.ready (C : Phase3CandidateClosure) : Prop :=
  C.r1MilestoneRecorded ∧ C.r2MilestoneRecorded ∧ C.r3MilestoneRecorded ∧
  C.r4MilestoneRecorded ∧ C.r5MilestoneRecorded ∧ C.r6MilestoneRecorded ∧
  C.r7MilestoneRecorded ∧ C.r3OmissionCorrected ∧ C.mathlibStillDeferred ∧
  C.publicBoundaryHeld

theorem phase3_candidate_closure_pack
    (C : Phase3CandidateClosure) :
    C.ready ↔ C.r1MilestoneRecorded ∧ C.r2MilestoneRecorded ∧ C.r3MilestoneRecorded ∧
      C.r4MilestoneRecorded ∧ C.r5MilestoneRecorded ∧ C.r6MilestoneRecorded ∧
      C.r7MilestoneRecorded ∧ C.r3OmissionCorrected ∧ C.mathlibStillDeferred ∧
      C.publicBoundaryHeld := by
  rfl

end MGAP4D
