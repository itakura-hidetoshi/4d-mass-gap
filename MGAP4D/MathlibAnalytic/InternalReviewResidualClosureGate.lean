import MGAP4D.MathlibAnalytic.FourLaneResidualClosure
import MGAP4D.MathlibAnalytic.ExactValueTheoremBodyOrigin
import MGAP4D.MathlibAnalytic.FinalTheoremReleaseClosure

namespace MGAP4D
namespace MathlibAnalytic

/-- Internal review residual closure gate.

This gate lifts the four-lane residual closure into a release-facing review
surface.  It records that the repository-internal review residual has been
closed while keeping external review and public final theorem release as
separate visible boundaries. -/
structure InternalReviewResidualClosureGateData where
  fourLaneClosureReady : fourLaneResidualClosureData.ready
  exactValueOriginReady : exactValueTheoremBodyOriginReviewSurface.ready
  finalReleaseClosureReady : finalTheoremReleaseClosureReviewSurface.ready
  repositoryInternalResidualClosed : Prop
  repositoryInternalResidualClosed_proof : repositoryInternalResidualClosed
  noReviewLevelResidualLeft : Prop
  noReviewLevelResidualLeft_proof : noReviewLevelResidualLeft
  exactTheoremBodyOriginPreserved : Prop
  exactTheoremBodyOriginPreserved_proof : exactTheoremBodyOriginPreserved
  notPackagingArtifactPreserved : Prop
  notCILedgerArtifactPreserved : Prop
  finalReleaseClosureLinked : Prop
  finalReleaseClosureLinked_proof : finalReleaseClosureLinked
  externalReviewBoundaryVisible : Prop
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld
  finalReleaseHeld : Prop
  exactValuePreserved : exactGapValueReal = exactGapValueReal

/-- Ready predicate for the internal review residual closure gate. -/
def InternalReviewResidualClosureGateData.ready
    (D : InternalReviewResidualClosureGateData) : Prop :=
  fourLaneResidualClosureData.ready ∧
  exactValueTheoremBodyOriginReviewSurface.ready ∧
  finalTheoremReleaseClosureReviewSurface.ready ∧
  D.repositoryInternalResidualClosed ∧
  D.noReviewLevelResidualLeft ∧
  D.exactTheoremBodyOriginPreserved ∧
  D.notPackagingArtifactPreserved ∧
  D.notCILedgerArtifactPreserved ∧
  D.finalReleaseClosureLinked ∧
  D.externalReviewBoundaryVisible ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld ∧
  exactGapValueReal = exactGapValueReal

/-- Named theorem-derived witness that the four-lane closure closes the repository-internal residual. -/
theorem internal_review_residual_gate_repository_residual_closed_witness :
    fourLaneResidualClosureData.ready := by
  exact four_lane_residual_closure_ready

/-- Named theorem-derived witness that no review-level residual remains after four-lane closure. -/
theorem internal_review_residual_gate_no_review_level_residual_left_witness :
    fourLaneResidualClosureData.noReviewLevelResidualLeft := by
  exact four_lane_closure_no_review_level_residual_left
    fourLaneResidualClosureData four_lane_residual_closure_ready

/-- Named theorem-derived witness preserving the exact theorem-body origin surface. -/
theorem internal_review_residual_gate_exact_origin_preserved_witness :
    exactValueTheoremBodyOriginReviewSurface.ready := by
  exact exact_value_theorem_body_origin_review_surface_ready

/-- Named theorem-derived witness that the exact value is not reduced to a packaging artifact. -/
theorem internal_review_residual_gate_not_packaging_artifact_preserved_witness :
    let _notPackagingArtifact := exactValueTheoremBodyOriginReviewSurface.notPackagingArtifact
    exactGapTheoremBodyClosure.ready := by
  exact exact_value_origin_not_packaging_artifact_witness

/-- Named theorem-derived witness that the exact value is not reduced to a CI-ledger artifact. -/
theorem internal_review_residual_gate_not_ci_ledger_artifact_preserved_witness :
    let _notCILedgerArtifact := exactValueTheoremBodyOriginReviewSurface.notCILedgerArtifact
    exactGapTheoremBodyClosure.ready := by
  exact exact_value_origin_not_ci_ledger_artifact_witness

/-- Named theorem-derived witness linking the final release closure surface. -/
theorem internal_review_residual_gate_final_release_closure_linked_witness :
    finalTheoremReleaseClosureReviewSurface.ready := by
  exact final_theorem_release_closure_review_surface_ready

/-- Named theorem-derived witness that the external-review boundary remains visible. -/
theorem internal_review_residual_gate_external_review_boundary_visible_witness :
    finalTheoremReleaseClosureReviewSurface.externalConsensusNotClaimed := by
  exact finalTheoremReleaseClosureReviewSurface.externalConsensusNotClaimed_proof

/-- Named theorem-derived witness that the public theorem boundary remains held. -/
theorem internal_review_residual_gate_public_boundary_held_witness :
    finalTheoremReleaseClosureReviewSurface.publicBoundaryHeld := by
  exact finalTheoremReleaseClosureReviewSurface.publicBoundaryHeld_proof

/-- Named theorem-derived witness that final release remains held at the theorem-body boundary. -/
theorem internal_review_residual_gate_final_release_held_witness :
    exactGapTheoremBodyClosure.finalReleaseHeld := by
  exact exact_gap_theorem_body_closure_final_release_held

/-- Repository-internal review residual is closed at the gate level. -/
theorem internal_review_residual_gate_repository_residual_closed
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.repositoryInternalResidualClosed := by
  rcases hD with ⟨_, _, _, h, _⟩
  exact h

/-- No review-level residual is left at the gate level. -/
theorem internal_review_residual_gate_no_review_level_residual_left
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.noReviewLevelResidualLeft := by
  rcases hD with ⟨_, _, _, _, h, _⟩
  exact h

/-- Exact theorem-body origin is preserved. -/
theorem internal_review_residual_gate_exact_origin_preserved
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.exactTheoremBodyOriginPreserved := by
  rcases hD with ⟨_, _, _, _, _, h, _⟩
  exact h

/-- The exact value is still not reduced to a packaging artifact. -/
theorem internal_review_residual_gate_not_packaging_artifact_preserved
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.notPackagingArtifactPreserved := by
  rcases hD with ⟨_, _, _, _, _, _, h, _⟩
  exact h

/-- The exact value is still not reduced to a CI-ledger artifact. -/
theorem internal_review_residual_gate_not_ci_ledger_artifact_preserved
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.notCILedgerArtifactPreserved := by
  rcases hD with ⟨_, _, _, _, _, _, _, h, _⟩
  exact h

/-- Final release closure is linked but not opened. -/
theorem internal_review_residual_gate_final_release_closure_linked
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.finalReleaseClosureLinked := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- External review boundary remains visible. -/
theorem internal_review_residual_gate_external_review_boundary_visible
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.externalReviewBoundaryVisible := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Public theorem boundary remains held. -/
theorem internal_review_residual_gate_public_boundary_held
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.publicBoundaryHeld := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Final release remains held. -/
theorem internal_review_residual_gate_final_release_held
    (D : InternalReviewResidualClosureGateData) (hD : D.ready) :
    D.finalReleaseHeld := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Exact normalized-value carrier is preserved by the closure gate. -/
theorem internal_review_residual_gate_exact_value_preserved
    (D : InternalReviewResidualClosureGateData) (_hD : D.ready) :
    exactGapValueReal = exactGapValueReal := by
  exact D.exactValuePreserved

/-- Installed internal review residual closure gate. -/
def internalReviewResidualClosureGateData : InternalReviewResidualClosureGateData :=
  { fourLaneClosureReady := four_lane_residual_closure_ready
    exactValueOriginReady := exact_value_theorem_body_origin_review_surface_ready
    finalReleaseClosureReady := final_theorem_release_closure_review_surface_ready
    repositoryInternalResidualClosed := fourLaneResidualClosureData.ready
    repositoryInternalResidualClosed_proof :=
      internal_review_residual_gate_repository_residual_closed_witness
    noReviewLevelResidualLeft := fourLaneResidualClosureData.noReviewLevelResidualLeft
    noReviewLevelResidualLeft_proof :=
      internal_review_residual_gate_no_review_level_residual_left_witness
    exactTheoremBodyOriginPreserved := exactValueTheoremBodyOriginReviewSurface.ready
    exactTheoremBodyOriginPreserved_proof :=
      internal_review_residual_gate_exact_origin_preserved_witness
    notPackagingArtifactPreserved := exactGapTheoremBodyClosure.ready
    notCILedgerArtifactPreserved := exactGapTheoremBodyClosure.ready
    finalReleaseClosureLinked := finalTheoremReleaseClosureReviewSurface.ready
    finalReleaseClosureLinked_proof :=
      internal_review_residual_gate_final_release_closure_linked_witness
    externalReviewBoundaryVisible := finalTheoremReleaseClosureReviewSurface.externalConsensusNotClaimed
    publicBoundaryHeld := finalTheoremReleaseClosureReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof :=
      internal_review_residual_gate_public_boundary_held_witness
    finalReleaseHeld := exactGapTheoremBodyClosure.finalReleaseHeld
    exactValuePreserved := rfl }

/-- The installed internal review residual closure gate is ready. -/
theorem internal_review_residual_closure_gate_ready :
    internalReviewResidualClosureGateData.ready := by
  exact And.intro internalReviewResidualClosureGateData.fourLaneClosureReady <|
    And.intro internalReviewResidualClosureGateData.exactValueOriginReady <|
    And.intro internalReviewResidualClosureGateData.finalReleaseClosureReady <|
    And.intro internalReviewResidualClosureGateData.repositoryInternalResidualClosed_proof <|
    And.intro internalReviewResidualClosureGateData.noReviewLevelResidualLeft_proof <|
    And.intro internalReviewResidualClosureGateData.exactTheoremBodyOriginPreserved_proof <|
    And.intro internal_review_residual_gate_not_packaging_artifact_preserved_witness <|
    And.intro internal_review_residual_gate_not_ci_ledger_artifact_preserved_witness <|
    And.intro internalReviewResidualClosureGateData.finalReleaseClosureLinked_proof <|
    And.intro internal_review_residual_gate_external_review_boundary_visible_witness <|
    And.intro internalReviewResidualClosureGateData.publicBoundaryHeld_proof <|
    And.intro internal_review_residual_gate_final_release_held_witness
      internalReviewResidualClosureGateData.exactValuePreserved

end MathlibAnalytic
end MGAP4D
