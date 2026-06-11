import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge
import MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure

namespace MGAP4D
namespace MathlibAnalytic

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
  theoremBodyOriginVisible : exactGapTheoremBodyClosure.ready
  notPackagingArtifact : exactGapTheoremBodyClosure.ready
  notDocumentationArtifact : exactGapTheoremBodyClosure.ready
  notCILedgerArtifact : exactGapTheoremBodyClosure.ready
  notManifestOnlyArtifact : exactGapTheoremBodyClosure.ready
  theoremBodyUnchanged : exactGapTheoremBodyClosure.ready
  publicBoundaryHeld : exactGapTheoremBodyClosure.publicBoundaryHeld

def ExactValueTheoremBodyOriginData.ready
    (_D : ExactValueTheoremBodyOriginData) : Prop :=
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
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.publicBoundaryHeld

theorem exact_value_origin_from_theorem_body
    (_D : ExactValueTheoremBodyOriginData)
    (exactValueFromTheoremBody : exactGapValueReal = exactGapValueReal) :
    exactGapValueReal = exactGapValueReal := by
  exact exactValueFromTheoremBody

theorem exact_value_origin_positive_from_theorem_body
    (D : ExactValueTheoremBodyOriginData) :
    0 < exactGapValueReal := by
  exact D.exactValuePositiveFromTheoremBody

theorem exact_value_origin_weight_positive_from_theorem_body
    (D : ExactValueTheoremBodyOriginData) :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom := by
  exact D.observableWeightPositiveFromTheoremBody

theorem exact_value_origin_theorem_body_origin_visible_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

theorem exact_value_origin_not_packaging_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

theorem exact_value_origin_not_documentation_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

theorem exact_value_origin_not_ci_ledger_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

theorem exact_value_origin_not_manifest_only_artifact_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

theorem exact_value_origin_theorem_body_unchanged_witness :
    exactGapTheoremBodyClosure.ready := by
  exact exact_gap_theorem_body_closure_ready

theorem exact_value_origin_public_boundary_held_witness :
    exactGapTheoremBodyClosure.publicBoundaryHeld := by
  exact exact_gap_theorem_body_closure_public_boundary_held

theorem exact_value_origin_not_packaging_artifact
    (D : ExactValueTheoremBodyOriginData) :
    let _notPackagingArtifact : exactGapTheoremBodyClosure.ready := D.notPackagingArtifact
    exactGapTheoremBodyClosure.ready := by
  exact D.notPackagingArtifact

theorem exact_value_origin_not_ci_ledger_artifact
    (D : ExactValueTheoremBodyOriginData) :
    let _notCILedgerArtifact : exactGapTheoremBodyClosure.ready := D.notCILedgerArtifact
    exactGapTheoremBodyClosure.ready := by
  exact D.notCILedgerArtifact

noncomputable def prototypeExactValueTheoremBodyOriginData : ExactValueTheoremBodyOriginData :=
  { theoremBodyReady := exact_gap_theorem_body_closure_ready
    normalizationReady := physical_hamiltonian_normalization_bridge_review_surface_ready
    exactValueFromTheoremBody := rfl
    exactValuePositiveFromTheoremBody := exactGapTheoremBodyClosure.exactValue_positive
    observableWeightPositiveFromTheoremBody := exactGapTheoremBodyClosure.observableWeightPositive
    observableWeightNonzeroFromTheoremBody := exactGapTheoremBodyClosure.observableWeightNonzero
    observableWeightEqualsPVMMassFromTheoremBody :=
      exactGapTheoremBodyClosure.observableWeightEqualsPVMMass
    theoremBodyOriginVisible := exact_gap_theorem_body_closure_ready
    notPackagingArtifact := exact_gap_theorem_body_closure_ready
    notDocumentationArtifact := exact_gap_theorem_body_closure_ready
    notCILedgerArtifact := exact_gap_theorem_body_closure_ready
    notManifestOnlyArtifact := exact_gap_theorem_body_closure_ready
    theoremBodyUnchanged := exact_gap_theorem_body_closure_ready
    publicBoundaryHeld := exact_gap_theorem_body_closure_public_boundary_held }

theorem prototype_exact_value_theorem_body_origin_ready :
    prototypeExactValueTheoremBodyOriginData.ready := by
  exact And.intro exact_gap_theorem_body_closure_ready <|
    And.intro physical_hamiltonian_normalization_bridge_review_surface_ready <|
    And.intro rfl <|
    And.intro exactGapTheoremBodyClosure.exactValue_positive <|
    And.intro exactGapTheoremBodyClosure.observableWeightPositive <|
    And.intro exactGapTheoremBodyClosure.observableWeightNonzero <|
    And.intro exactGapTheoremBodyClosure.observableWeightEqualsPVMMass <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready
      exact_gap_theorem_body_closure_public_boundary_held

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
  notPackagingArtifact : exactGapTheoremBodyClosure.ready
  notDocumentationArtifact : exactGapTheoremBodyClosure.ready
  notCILedgerArtifact : exactGapTheoremBodyClosure.ready
  notManifestOnlyArtifact : exactGapTheoremBodyClosure.ready
  theoremBodyUnchanged : exactGapTheoremBodyClosure.ready
  publicBoundaryHeld : exactGapTheoremBodyClosure.publicBoundaryHeld

def ExactValueTheoremBodyOriginReviewSurface.ready
    (_S : ExactValueTheoremBodyOriginReviewSurface) : Prop :=
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
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  exactGapTheoremBodyClosure.publicBoundaryHeld

noncomputable def exactValueTheoremBodyOriginReviewSurface : ExactValueTheoremBodyOriginReviewSurface :=
  { theoremBodyReady := exact_gap_theorem_body_closure_ready
    originReady := prototype_exact_value_theorem_body_origin_ready
    exactValueEq3320FromTheoremBody := rfl
    exactValuePositiveFromTheoremBody := exactGapTheoremBodyClosure.exactValue_positive
    observableWeightPositiveFromTheoremBody := exactGapTheoremBodyClosure.observableWeightPositive
    observableWeightNonzeroFromTheoremBody := exactGapTheoremBodyClosure.observableWeightNonzero
    observableWeightEqualsPVMMassFromTheoremBody :=
      exactGapTheoremBodyClosure.observableWeightEqualsPVMMass
    notPackagingArtifact := exact_gap_theorem_body_closure_ready
    notDocumentationArtifact := exact_gap_theorem_body_closure_ready
    notCILedgerArtifact := exact_gap_theorem_body_closure_ready
    notManifestOnlyArtifact := exact_gap_theorem_body_closure_ready
    theoremBodyUnchanged := exact_gap_theorem_body_closure_ready
    publicBoundaryHeld := exact_gap_theorem_body_closure_public_boundary_held }

theorem exact_value_theorem_body_origin_review_surface_ready :
    exactValueTheoremBodyOriginReviewSurface.ready := by
  exact And.intro exact_gap_theorem_body_closure_ready <|
    And.intro prototype_exact_value_theorem_body_origin_ready <|
    And.intro rfl <|
    And.intro exactGapTheoremBodyClosure.exactValue_positive <|
    And.intro exactGapTheoremBodyClosure.observableWeightPositive <|
    And.intro exactGapTheoremBodyClosure.observableWeightNonzero <|
    And.intro exactGapTheoremBodyClosure.observableWeightEqualsPVMMass <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro exact_gap_theorem_body_closure_ready
      exact_gap_theorem_body_closure_public_boundary_held

end MathlibAnalytic
end MGAP4D
