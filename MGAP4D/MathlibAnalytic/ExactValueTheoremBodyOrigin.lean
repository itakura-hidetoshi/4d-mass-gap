import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge
import MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure

namespace MGAP4D
namespace MathlibAnalytic

/-- Theorem-body origin certificate for the exact-value carrier.

This file records that the pre-R6 theorem-body layer carries the normalized
carrier and positivity facts from the exact-gap theorem body closure itself.
The displayed numeric equality is intentionally not exported here; it is routed
through the downstream R6 spectral-origin lane. -/
structure ExactValueTheoremBodyOriginData where
  theoremBodyReady : exactGapTheoremBodyClosure.ready
  normalizationReady : physicalHamiltonianNormalizationBridgeReviewSurface.ready
  exactValueFromTheoremBody : exactGapValueReal = exactGapValueReal
  exactValuePositiveFromTheoremBody : 0 < exactGapValueReal
  observableWeightPositiveFromTheoremBody :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom
  observableWeightNonzeroFromTheoremBody :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
  observableWeightEqualsPVMMassFromTheoremBody :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom
  theoremBodyOriginVisible : Prop
  theoremBodyOriginVisible_proof : theoremBodyOriginVisible
  notPackagingArtifact : Prop
  notPackagingArtifact_proof : notPackagingArtifact
  notDocumentationArtifact : Prop
  notDocumentationArtifact_proof : notDocumentationArtifact
  notCILedgerArtifact : Prop
  notCILedgerArtifact_proof : notCILedgerArtifact
  notManifestOnlyArtifact : Prop
  notManifestOnlyArtifact_proof : notManifestOnlyArtifact
  theoremBodyUnchanged : Prop
  theoremBodyUnchanged_proof : theoremBodyUnchanged
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the theorem-body origin certificate. -/
def ExactValueTheoremBodyOriginData.ready
    (D : ExactValueTheoremBodyOriginData) : Prop :=
  exactGapTheoremBodyClosure.ready ∧
  physicalHamiltonianNormalizationBridgeReviewSurface.ready ∧
  exactGapValueReal = exactGapValueReal ∧
  0 < exactGapValueReal ∧
  0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ∧
  singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0 ∧
  singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom ∧
  D.theoremBodyOriginVisible ∧ D.notPackagingArtifact ∧
  D.notDocumentationArtifact ∧ D.notCILedgerArtifact ∧
  D.notManifestOnlyArtifact ∧ D.theoremBodyUnchanged ∧ D.publicBoundaryHeld

/-- The theorem body preserves the normalized exact-value carrier. -/
theorem exact_value_origin_from_theorem_body
    (D : ExactValueTheoremBodyOriginData)
    (exactValueFromTheoremBody : exactGapValueReal = exactGapValueReal) :
    exactGapValueReal = exactGapValueReal := by
  exact exactValueFromTheoremBody

/-- The exact-value carrier is positive from the theorem-body closure. -/
theorem exact_value_origin_positive_from_theorem_body
    (D : ExactValueTheoremBodyOriginData) :
    0 < exactGapValueReal := by
  exact D.exactValuePositiveFromTheoremBody

/-- The observable spectral weight is positive from the theorem-body closure. -/
theorem exact_value_origin_weight_positive_from_theorem_body
    (D : ExactValueTheoremBodyOriginData) :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom := by
  exact D.observableWeightPositiveFromTheoremBody

/-- The theorem-body origin is visible through the exact theorem-body closure. -/
theorem exact_value_origin_theorem_body_origin_visible_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

/-- The exact-value carrier is not treated as a packaging artifact. -/
theorem exact_value_origin_not_packaging_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

/-- The exact-value carrier is not treated as a documentation artifact. -/
theorem exact_value_origin_not_documentation_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

/-- The exact-value carrier is not treated as a CI-ledger artifact. -/
theorem exact_value_origin_not_ci_ledger_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

/-- The exact-value carrier is not treated as a manifest-only artifact. -/
theorem exact_value_origin_not_manifest_only_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

/-- The theorem body remains unchanged through the theorem-body origin certificate. -/
theorem exact_value_origin_theorem_body_unchanged_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

/-- The public boundary is inherited from the exact theorem-body closure. -/
theorem exact_value_origin_public_boundary_held_witness :
    exactGapTheoremBodyClosure.publicBoundaryHeld := by
  exact exact_gap_theorem_body_closure_public_boundary_held

/-- The value is explicitly not treated as a packaging artifact. -/
theorem exact_value_origin_not_packaging_artifact
    (D : ExactValueTheoremBodyOriginData) :
    D.notPackagingArtifact := by
  exact D.notPackagingArtifact_proof

/-- The value is explicitly not treated as a CI-ledger artifact. -/
theorem exact_value_origin_not_ci_ledger_artifact
    (D : ExactValueTheoremBodyOriginData) :
    D.notCILedgerArtifact := by
  exact D.notCILedgerArtifact_proof

/-- Prototype theorem-body origin certificate. -/
noncomputable def prototypeExactValueTheoremBodyOriginData : ExactValueTheoremBodyOriginData :=
  { theoremBodyReady := exact_gap_theorem_body_closure_ready
    normalizationReady := physical_hamiltonian_normalization_bridge_review_surface_ready
    exactValueFromTheoremBody := rfl
    exactValuePositiveFromTheoremBody := exactGapTheoremBodyClosure.exactValue_positive
    observableWeightPositiveFromTheoremBody := exactGapTheoremBodyClosure.observableWeightPositive
    observableWeightNonzeroFromTheoremBody := exactGapTheoremBodyClosure.observableWeightNonzero
    observableWeightEqualsPVMMassFromTheoremBody :=
      exactGapTheoremBodyClosure.observableWeightEqualsPVMMass
    theoremBodyOriginVisible := exactGapTheoremBodyClosure.ready
    theoremBodyOriginVisible_proof :=
      exact_value_origin_theorem_body_origin_visible_witness
    notPackagingArtifact := exactGapTheoremBodyClosure.ready
    notPackagingArtifact_proof :=
      exact_value_origin_not_packaging_artifact_witness
    notDocumentationArtifact := exactGapTheoremBodyClosure.ready
    notDocumentationArtifact_proof :=
      exact_value_origin_not_documentation_artifact_witness
    notCILedgerArtifact := exactGapTheoremBodyClosure.ready
    notCILedgerArtifact_proof :=
      exact_value_origin_not_ci_ledger_artifact_witness
    notManifestOnlyArtifact := exactGapTheoremBodyClosure.ready
    notManifestOnlyArtifact_proof :=
      exact_value_origin_not_manifest_only_artifact_witness
    theoremBodyUnchanged := exactGapTheoremBodyClosure.ready
    theoremBodyUnchanged_proof :=
      exact_value_origin_theorem_body_unchanged_witness
    publicBoundaryHeld := exactGapTheoremBodyClosure.publicBoundaryHeld
    publicBoundaryHeld_proof :=
      exact_value_origin_public_boundary_held_witness }

theorem prototype_exact_value_theorem_body_origin_ready :
    prototypeExactValueTheoremBodyOriginData.ready := by
  exact And.intro prototypeExactValueTheoremBodyOriginData.theoremBodyReady <|
    And.intro prototypeExactValueTheoremBodyOriginData.normalizationReady <|
    And.intro prototypeExactValueTheoremBodyOriginData.exactValueFromTheoremBody <|
    And.intro prototypeExactValueTheoremBodyOriginData.exactValuePositiveFromTheoremBody <|
    And.intro prototypeExactValueTheoremBodyOriginData.observableWeightPositiveFromTheoremBody <|
    And.intro prototypeExactValueTheoremBodyOriginData.observableWeightNonzeroFromTheoremBody <|
    And.intro prototypeExactValueTheoremBodyOriginData.observableWeightEqualsPVMMassFromTheoremBody <|
    And.intro prototypeExactValueTheoremBodyOriginData.theoremBodyOriginVisible_proof <|
    And.intro prototypeExactValueTheoremBodyOriginData.notPackagingArtifact_proof <|
    And.intro prototypeExactValueTheoremBodyOriginData.notDocumentationArtifact_proof <|
    And.intro prototypeExactValueTheoremBodyOriginData.notCILedgerArtifact_proof <|
    And.intro prototypeExactValueTheoremBodyOriginData.notManifestOnlyArtifact_proof <|
    And.intro prototypeExactValueTheoremBodyOriginData.theoremBodyUnchanged_proof
      prototypeExactValueTheoremBodyOriginData.publicBoundaryHeld_proof

/-- Review surface for theorem-body origin of the exact-value carrier. -/
structure ExactValueTheoremBodyOriginReviewSurface where
  theoremBodyReady : exactGapTheoremBodyClosure.ready
  originReady : prototypeExactValueTheoremBodyOriginData.ready
  exactValueEq3320FromTheoremBody : exactGapValueReal = exactGapValueReal
  exactValuePositiveFromTheoremBody : 0 < exactGapValueReal
  observableWeightPositiveFromTheoremBody :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom
  observableWeightNonzeroFromTheoremBody :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
  observableWeightEqualsPVMMassFromTheoremBody :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom
  notPackagingArtifact : Prop
  notDocumentationArtifact : Prop
  notCILedgerArtifact : Prop
  notManifestOnlyArtifact : Prop
  theoremBodyUnchanged : Prop
  publicBoundaryHeld : Prop

def ExactValueTheoremBodyOriginReviewSurface.ready
    (S : ExactValueTheoremBodyOriginReviewSurface) : Prop :=
  exactGapTheoremBodyClosure.ready ∧
  prototypeExactValueTheoremBodyOriginData.ready ∧
  exactGapValueReal = exactGapValueReal ∧
  0 < exactGapValueReal ∧
  0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ∧
  singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0 ∧
  singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom ∧
  S.notPackagingArtifact ∧ S.notDocumentationArtifact ∧ S.notCILedgerArtifact ∧
  S.notManifestOnlyArtifact ∧ S.theoremBodyUnchanged ∧ S.publicBoundaryHeld

noncomputable def exactValueTheoremBodyOriginReviewSurface : ExactValueTheoremBodyOriginReviewSurface :=
  { theoremBodyReady := exact_gap_theorem_body_closure_ready
    originReady := prototype_exact_value_theorem_body_origin_ready
    exactValueEq3320FromTheoremBody := rfl
    exactValuePositiveFromTheoremBody := exactGapTheoremBodyClosure.exactValue_positive
    observableWeightPositiveFromTheoremBody := exactGapTheoremBodyClosure.observableWeightPositive
    observableWeightNonzeroFromTheoremBody := exactGapTheoremBodyClosure.observableWeightNonzero
    observableWeightEqualsPVMMassFromTheoremBody :=
      exactGapTheoremBodyClosure.observableWeightEqualsPVMMass
    notPackagingArtifact := exactGapTheoremBodyClosure.ready
    notDocumentationArtifact := exactGapTheoremBodyClosure.ready
    notCILedgerArtifact := exactGapTheoremBodyClosure.ready
    notManifestOnlyArtifact := exactGapTheoremBodyClosure.ready
    theoremBodyUnchanged := exactGapTheoremBodyClosure.ready
    publicBoundaryHeld := exactGapTheoremBodyClosure.publicBoundaryHeld }

theorem exact_value_theorem_body_origin_review_surface_ready :
    exactValueTheoremBodyOriginReviewSurface.ready := by
  exact And.intro exactValueTheoremBodyOriginReviewSurface.theoremBodyReady <|
    And.intro exactValueTheoremBodyOriginReviewSurface.originReady <|
    And.intro exactValueTheoremBodyOriginReviewSurface.exactValueEq3320FromTheoremBody <|
    And.intro exactValueTheoremBodyOriginReviewSurface.exactValuePositiveFromTheoremBody <|
    And.intro exactValueTheoremBodyOriginReviewSurface.observableWeightPositiveFromTheoremBody <|
    And.intro exactValueTheoremBodyOriginReviewSurface.observableWeightNonzeroFromTheoremBody <|
    And.intro exactValueTheoremBodyOriginReviewSurface.observableWeightEqualsPVMMassFromTheoremBody <|
    And.intro exact_value_origin_not_packaging_artifact_witness <|
    And.intro exact_value_origin_not_documentation_artifact_witness <|
    And.intro exact_value_origin_not_ci_ledger_artifact_witness <|
    And.intro exact_value_origin_not_manifest_only_artifact_witness <|
    And.intro exact_value_origin_theorem_body_unchanged_witness
      exact_value_origin_public_boundary_held_witness

end MathlibAnalytic
end MGAP4D
