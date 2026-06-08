import MGAP4D.ExactGapResidualMap

namespace MGAP4D

/-- Ordered resolution targets for the exact-gap residual map.

The order is intentionally conservative: first replace structural surfaces,
then install the operator-theoretic Hamiltonian body, then define the gap as an
infimum, then prove the lower bound, construct the eigenvector, connect the
observable spectral projection, and finally move through the Mathlib adoption
bridge. -/
inductive ExactGapResidualResolutionTarget where
  | structuralSurfaceRealization
  | hphysSelfAdjointSemiboundedDomain
  | gapInfimumDefinition
  | lowerBoundProofBody
  | eigenvectorConstruction
  | observableSpectralProjection
  | mathlibAdoptionBridge
  deriving Repr, DecidableEq

/-- A pre-Mathlib resolution plan for the exact-gap residual map.

This is not the analytic theorem body itself.  It is the CI-visible plan that
orders the seven residual replacement targets while preserving the exact-gap
release-readiness boundary. -/
structure ExactGapResidualResolutionPlan where
  residualMap : ExactGapResidualMap
  residualMapReady : residualMap.ready
  structuralSurfaceRealizationPlanned : residualMap.residualStructuralSurfaceRealization
  hphysSelfAdjointSemiboundedDomainPlanned : residualMap.residualHphysSelfAdjointSemiboundedDomain
  gapInfimumDefinitionPlanned : residualMap.residualGapInfimumDefinition
  lowerBoundProofBodyPlanned : residualMap.residualLowerBoundProofBody
  eigenvectorConstructionPlanned : residualMap.residualEigenvectorConstruction
  observableSpectralProjectionPlanned : residualMap.residualObservableSpectralProjection
  mathlibAdoptionBridgePlanned : residualMap.residualMathlibAdoptionBridge
  conservativeOrderingVisible : Prop
  resolutionPlanVisible : Prop
  exactGapValue3320 : residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20
  finalReleaseHeld : residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld
  publicBoundaryLocked : residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked
  noAutoRelease : residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease
  theoremBoundaryHeld : residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld

/-- Ready predicate for the residual resolution plan, with proof fields expanded. -/
def ExactGapResidualResolutionPlan.ready
    (P : ExactGapResidualResolutionPlan) : Prop :=
  P.residualMap.ready ∧ P.residualMap.residualStructuralSurfaceRealization ∧
  P.residualMap.residualHphysSelfAdjointSemiboundedDomain ∧
  P.residualMap.residualGapInfimumDefinition ∧
  P.residualMap.residualLowerBoundProofBody ∧
  P.residualMap.residualEigenvectorConstruction ∧
  P.residualMap.residualObservableSpectralProjection ∧
  P.residualMap.residualMathlibAdoptionBridge ∧
  P.conservativeOrderingVisible ∧ P.resolutionPlanVisible ∧
  P.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
  P.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
  P.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
  P.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
  P.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld

def exactGap3320ResidualResolutionPlan : ExactGapResidualResolutionPlan :=
  { residualMap := exactGap3320ResidualMap
    residualMapReady := exact_gap_3320_residual_map_ready
    structuralSurfaceRealizationPlanned := exact_gap_3320_residual_structural_surface_realization
    hphysSelfAdjointSemiboundedDomainPlanned := exact_gap_3320_residual_hphys_self_adjoint_semibounded_domain
    gapInfimumDefinitionPlanned := exact_gap_3320_residual_gap_infimum_definition
    lowerBoundProofBodyPlanned := exact_gap_3320_residual_lower_bound_proof_body
    eigenvectorConstructionPlanned := exact_gap_3320_residual_eigenvector_construction
    observableSpectralProjectionPlanned := exact_gap_3320_residual_observable_spectral_projection
    mathlibAdoptionBridgePlanned := exact_gap_3320_residual_mathlib_adoption_bridge
    conservativeOrderingVisible := True
    resolutionPlanVisible := True
    exactGapValue3320 := exact_gap_3320_residual_map_value
    finalReleaseHeld := exact_gap_3320_residual_map_release_held
    publicBoundaryLocked := exact_gap_3320_residual_map_public_boundary_locked
    noAutoRelease := exact_gap_3320_residual_map_no_auto_release
    theoremBoundaryHeld := by trivial }

theorem exact_gap_residual_resolution_plan_pack
    (P : ExactGapResidualResolutionPlan) :
    P.ready ↔ P.residualMap.ready ∧ P.residualMap.residualStructuralSurfaceRealization ∧
      P.residualMap.residualHphysSelfAdjointSemiboundedDomain ∧
      P.residualMap.residualGapInfimumDefinition ∧
      P.residualMap.residualLowerBoundProofBody ∧
      P.residualMap.residualEigenvectorConstruction ∧
      P.residualMap.residualObservableSpectralProjection ∧
      P.residualMap.residualMathlibAdoptionBridge ∧
      P.conservativeOrderingVisible ∧ P.resolutionPlanVisible ∧
      P.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 ∧
      P.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld ∧
      P.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked ∧
      P.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease ∧
      P.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.theoremBoundaryHeld := by
  rfl

theorem exact_gap_3320_residual_resolution_plan_ready :
    exactGap3320ResidualResolutionPlan.ready := by
  exact And.intro exact_gap_3320_residual_map_ready <|
    And.intro exact_gap_3320_residual_structural_surface_realization <|
    And.intro exact_gap_3320_residual_hphys_self_adjoint_semibounded_domain <|
    And.intro exact_gap_3320_residual_gap_infimum_definition <|
    And.intro exact_gap_3320_residual_lower_bound_proof_body <|
    And.intro exact_gap_3320_residual_eigenvector_construction <|
    And.intro exact_gap_3320_residual_observable_spectral_projection <|
    And.intro exact_gap_3320_residual_mathlib_adoption_bridge <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro exact_gap_3320_residual_map_value <|
    And.intro exact_gap_3320_residual_map_release_held <|
    And.intro exact_gap_3320_residual_map_public_boundary_locked <|
    And.intro exact_gap_3320_residual_map_no_auto_release True.intro

theorem exact_gap_3320_residual_resolution_plan_value :
    exactGap3320ResidualResolutionPlan.residualMap.releaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 := by
  exact exact_gap_3320_residual_map_value

theorem exact_gap_3320_residual_resolution_plan_release_held :
    exactGap3320ResidualResolutionPlan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.finalReleaseHeld := by
  exact exact_gap_3320_residual_map_release_held

theorem exact_gap_3320_residual_resolution_plan_public_boundary_locked :
    exactGap3320ResidualResolutionPlan.residualMap.releaseReadiness.auditClosure.exactGap.sandwich.r1r7Completion.publicBoundaryLocked := by
  exact exact_gap_3320_residual_map_public_boundary_locked

theorem exact_gap_3320_residual_resolution_plan_no_auto_release :
    exactGap3320ResidualResolutionPlan.residualMap.releaseReadiness.auditClosure.publicBoundary.exactGapDoesNotOpenFinalRelease := by
  exact exact_gap_3320_residual_map_no_auto_release

theorem exact_gap_3320_residual_resolution_plan_structural_first :
    exactGap3320ResidualResolutionPlan.residualMap.residualStructuralSurfaceRealization := by
  exact exact_gap_3320_residual_structural_surface_realization

theorem exact_gap_3320_residual_resolution_plan_mathlib_last :
    exactGap3320ResidualResolutionPlan.residualMap.residualMathlibAdoptionBridge := by
  exact exact_gap_3320_residual_mathlib_adoption_bridge

end MGAP4D
