import MGAP4D.Phase3CandidateClosure

namespace MGAP4D

structure Phase3CIConfirmationClosure where
  candidateClosureReady : Prop
  prCiObservedGreen : Prop
  manualMainCiObservedGreen : Prop
  observationPrClosedUnmerged : Prop
  mathlibStillDeferred : Prop
  lakefileMathlibUnchanged : Prop
  publicBoundaryHeld : Prop

def Phase3CIConfirmationClosure.ready (C : Phase3CIConfirmationClosure) : Prop :=
  C.candidateClosureReady ∧ C.prCiObservedGreen ∧ C.manualMainCiObservedGreen ∧
  C.observationPrClosedUnmerged ∧ C.mathlibStillDeferred ∧
  C.lakefileMathlibUnchanged ∧ C.publicBoundaryHeld

theorem phase3_ci_confirmation_closure_pack
    (C : Phase3CIConfirmationClosure) :
    C.ready ↔ C.candidateClosureReady ∧ C.prCiObservedGreen ∧ C.manualMainCiObservedGreen ∧
      C.observationPrClosedUnmerged ∧ C.mathlibStillDeferred ∧
      C.lakefileMathlibUnchanged ∧ C.publicBoundaryHeld := by
  rfl

end MGAP4D
