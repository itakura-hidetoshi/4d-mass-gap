import MGAP4D.IndependentReplayProtocolGlobalScopeCorrection

namespace MGAP4D

structure ExternalAuditNoteGate where
  independentReplayProtocolGlobalScopeCorrectionGreen : Prop
  externalAuditNoteSurfaceVisible : Prop
  reviewerCommentSurfaceVisible : Prop
  unresolvedIssueSurfaceVisible : Prop
  objectionSurfaceVisible : Prop
  independentReplayReferenceSurfaceVisible : Prop
  appendOnlyAuditNotePolicyVisible : Prop
  externalAuditNoteNotTheoremCompletion : Prop
  externalAuditNoteNotFinalRelease : Prop
  externalAuditNoteDoesNotIntroduceMathlib : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionsNotClaimed : Prop

def ExternalAuditNoteGate.ready
    (G : ExternalAuditNoteGate) : Prop :=
  G.independentReplayProtocolGlobalScopeCorrectionGreen ∧
  G.externalAuditNoteSurfaceVisible ∧ G.reviewerCommentSurfaceVisible ∧
  G.unresolvedIssueSurfaceVisible ∧ G.objectionSurfaceVisible ∧
  G.independentReplayReferenceSurfaceVisible ∧ G.appendOnlyAuditNotePolicyVisible ∧
  G.externalAuditNoteNotTheoremCompletion ∧ G.externalAuditNoteNotFinalRelease ∧
  G.externalAuditNoteDoesNotIntroduceMathlib ∧ G.finalGapReleaseNotUnlocked ∧
  G.publicBoundaryHeld ∧ G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
  G.theoremCompletionsNotClaimed

theorem external_audit_note_gate_pack
    (G : ExternalAuditNoteGate) :
    G.ready ↔ G.independentReplayProtocolGlobalScopeCorrectionGreen ∧
      G.externalAuditNoteSurfaceVisible ∧ G.reviewerCommentSurfaceVisible ∧
      G.unresolvedIssueSurfaceVisible ∧ G.objectionSurfaceVisible ∧
      G.independentReplayReferenceSurfaceVisible ∧ G.appendOnlyAuditNotePolicyVisible ∧
      G.externalAuditNoteNotTheoremCompletion ∧ G.externalAuditNoteNotFinalRelease ∧
      G.externalAuditNoteDoesNotIntroduceMathlib ∧ G.finalGapReleaseNotUnlocked ∧
      G.publicBoundaryHeld ∧ G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
      G.theoremCompletionsNotClaimed := by
  rfl

end MGAP4D
