import MGAP4D.ExactGapStructuralSurfaceRealization
import MGAP4D.MathlibAnalytic.ExactValueTheoremBodyOrigin

namespace MGAP4D

/-- A bridge from the pre-Mathlib exact-gap structural surface to the
Mathlib-analytic theorem-body origin certificate.

This bridge is deliberately non-releasing.  It records that the structural
surface now has a theorem-body origin witness for the exact value and observable
weight positivity, while preserving the release hold and public-boundary lock. -/
structure ExactGapTheoremBodyOriginBridge where
  structuralSurface : ExactGapStructuralSurfaceRealization
  structuralSurfaceReady : structuralSurface.ready
  theoremBodyOriginReady : MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.ready
  theoremBodyClosureReady : MathlibAnalytic.exactGapTheoremBodyClosure.ready
  exactValueFromTheoremBody : MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20
  exactValuePositiveFromTheoremBody : 0 < MathlibAnalytic.exactGapValueReal
  observableWeightPositiveFromTheoremBody :
    0 < MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.exactAtom
  observableWeightNonzeroFromTheoremBody :
    MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
  bridgeVisible : Prop
  finalReleaseHeld : structuralSurface.finalReleaseHeld
  publicBoundaryLocked : structuralSurface.publicBoundaryLocked
  noAutoRelease : structuralSurface.noAutoRelease
  theoremBoundaryHeld : structuralSurface.theoremBoundaryHeld

/-- Readiness re-expands proof-carrying fields to their underlying propositions. -/
def ExactGapTheoremBodyOriginBridge.ready
    (B : ExactGapTheoremBodyOriginBridge) : Prop :=
  B.structuralSurface.ready ∧
  MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.ready ∧
  MathlibAnalytic.exactGapTheoremBodyClosure.ready ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  0 < MathlibAnalytic.exactGapValueReal ∧
  0 < MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.exactAtom ∧
  MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0 ∧
  B.bridgeVisible ∧ B.structuralSurface.finalReleaseHeld ∧
  B.structuralSurface.publicBoundaryLocked ∧ B.structuralSurface.noAutoRelease ∧
  B.structuralSurface.theoremBoundaryHeld

noncomputable def exactGap3320TheoremBodyOriginBridge : ExactGapTheoremBodyOriginBridge :=
  { structuralSurface := exactGap3320StructuralSurfaceRealization
    structuralSurfaceReady := exact_gap_3320_structural_surface_realization_ready
    theoremBodyOriginReady := MathlibAnalytic.exact_value_theorem_body_origin_review_surface_ready
    theoremBodyClosureReady := MathlibAnalytic.exact_gap_theorem_body_closure_ready
    exactValueFromTheoremBody :=
      MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.exactValueEq3320FromTheoremBody
    exactValuePositiveFromTheoremBody :=
      MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.exactValuePositiveFromTheoremBody
    observableWeightPositiveFromTheoremBody :=
      MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.observableWeightPositiveFromTheoremBody
    observableWeightNonzeroFromTheoremBody :=
      MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.observableWeightNonzeroFromTheoremBody
    bridgeVisible := True
    finalReleaseHeld := exact_gap_3320_structural_surface_release_held
    publicBoundaryLocked := exact_gap_3320_structural_surface_public_boundary_locked
    noAutoRelease := exact_gap_3320_structural_surface_no_auto_release
    theoremBoundaryHeld := by trivial }

theorem exact_gap_theorem_body_origin_bridge_pack
    (B : ExactGapTheoremBodyOriginBridge) :
    B.ready ↔ B.structuralSurface.ready ∧
      MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.ready ∧
      MathlibAnalytic.exactGapTheoremBodyClosure.ready ∧
      MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
      0 < MathlibAnalytic.exactGapValueReal ∧
      0 < MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
        MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
        MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.exactAtom ∧
      MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
        MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
        MathlibAnalytic.singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0 ∧
      B.bridgeVisible ∧ B.structuralSurface.finalReleaseHeld ∧
      B.structuralSurface.publicBoundaryLocked ∧ B.structuralSurface.noAutoRelease ∧
      B.structuralSurface.theoremBoundaryHeld := by
  rfl

theorem exact_gap_3320_theorem_body_origin_bridge_ready :
    exactGap3320TheoremBodyOriginBridge.ready := by
  exact And.intro exact_gap_3320_structural_surface_realization_ready <|
    And.intro MathlibAnalytic.exact_value_theorem_body_origin_review_surface_ready <|
    And.intro MathlibAnalytic.exact_gap_theorem_body_closure_ready <|
    And.intro MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.exactValueEq3320FromTheoremBody <|
    And.intro MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.exactValuePositiveFromTheoremBody <|
    And.intro MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.observableWeightPositiveFromTheoremBody <|
    And.intro MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.observableWeightNonzeroFromTheoremBody <|
    And.intro True.intro <|
    And.intro exact_gap_3320_structural_surface_release_held <|
    And.intro exact_gap_3320_structural_surface_public_boundary_locked <|
    And.intro exact_gap_3320_structural_surface_no_auto_release True.intro

theorem exact_gap_3320_theorem_body_origin_bridge_value :
    MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 := by
  exact MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.exactValueEq3320FromTheoremBody

theorem exact_gap_3320_theorem_body_origin_bridge_positive :
    0 < MathlibAnalytic.exactGapValueReal := by
  exact MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface.exactValuePositiveFromTheoremBody

theorem exact_gap_3320_theorem_body_origin_bridge_release_held :
    exactGap3320TheoremBodyOriginBridge.finalReleaseHeld := by
  exact exact_gap_3320_structural_surface_release_held

theorem exact_gap_3320_theorem_body_origin_bridge_public_boundary_locked :
    exactGap3320TheoremBodyOriginBridge.publicBoundaryLocked := by
  exact exact_gap_3320_structural_surface_public_boundary_locked

theorem exact_gap_3320_theorem_body_origin_bridge_no_auto_release :
    exactGap3320TheoremBodyOriginBridge.noAutoRelease := by
  exact exact_gap_3320_structural_surface_no_auto_release

end MGAP4D
