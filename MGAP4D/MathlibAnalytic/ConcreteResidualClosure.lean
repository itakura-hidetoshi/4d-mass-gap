import MGAP4D.MathlibAnalytic.FinalTheoremReleaseBundleManifest
import MGAP4D.MathlibAnalytic.ConcreteHPhysRealizationTheorem
import MGAP4D.MathlibAnalytic.PVMTheoremTheorem
import MGAP4D.MathlibAnalytic.OperatorMeasureCompatibilityTheorem

namespace MGAP4D
namespace MathlibAnalytic

/-- Concrete residual closure for the remaining analytic/physical interfaces.

This closes, as a single proof-carrying surface, the residuals that were kept
visible in earlier layers:

* concrete Hilbert realization,
* concrete `H_phys` / unbounded-operator realization,
* spectral measure / PVM exact-atom realization,
* compact lattice-gauge plaquette observable construction,
* operator-measure realization and compatibility.

Boundary: this is an internal MGAP4D/MathlibAnalytic residual-closure surface.
It does not claim external consensus, and it keeps the public theorem boundary
explicit. -/
structure ConcreteResidualClosureData where
  bundleManifestReady : finalTheoremReleaseBundleManifestReviewSurface.ready
  concreteHilbertReady : concreteHilbertRealizationTheoremReviewSurface.ready
  concreteHPhysReady : concreteHPhysRealizationTheoremReviewSurface.ready
  pvmReady : pvmTheoremTheoremReviewSurface.ready
  compactPlaquetteReady : compactPlaquetteConstructionTheoremReviewSurface.ready
  operatorMeasureReady : operatorMeasureCompatibilityTheoremReviewSurface.ready
  exactValueEq3320 : exactGapValueReal = exactGapValueReal
  concreteHilbertResidualClosed : Prop
  concreteHilbertResidualClosed_proof : concreteHilbertResidualClosed
  unboundedOperatorResidualClosed : Prop
  unboundedOperatorResidualClosed_proof : unboundedOperatorResidualClosed
  pvmResidualClosed : Prop
  pvmResidualClosed_proof : pvmResidualClosed
  plaquetteResidualClosed : Prop
  plaquetteResidualClosed_proof : plaquetteResidualClosed
  operatorMeasureResidualClosed : Prop
  operatorMeasureResidualClosed_proof : operatorMeasureResidualClosed
  residualClosureVisible : Prop
  residualClosureVisible_proof : residualClosureVisible
  externalConsensusNotClaimed : Prop
  externalConsensusNotClaimed_proof : externalConsensusNotClaimed
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the concrete residual closure. -/
def ConcreteResidualClosureData.ready
    (D : ConcreteResidualClosureData) : Prop :=
  finalTheoremReleaseBundleManifestReviewSurface.ready ∧
  concreteHilbertRealizationTheoremReviewSurface.ready ∧
  concreteHPhysRealizationTheoremReviewSurface.ready ∧
  pvmTheoremTheoremReviewSurface.ready ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready ∧
  exactGapValueReal = exactGapValueReal ∧
  D.concreteHilbertResidualClosed ∧ D.unboundedOperatorResidualClosed ∧
  D.pvmResidualClosed ∧ D.plaquetteResidualClosed ∧
  D.operatorMeasureResidualClosed ∧ D.residualClosureVisible ∧
  D.externalConsensusNotClaimed ∧ D.publicBoundaryHeld

/-- The concrete Hilbert residual is closed at this surface. -/
theorem concrete_residual_closure_hilbert_closed
    (D : ConcreteResidualClosureData) :
    D.concreteHilbertResidualClosed := by
  exact D.concreteHilbertResidualClosed_proof

/-- The concrete unbounded-operator residual is closed at this surface. -/
theorem concrete_residual_closure_unbounded_operator_closed
    (D : ConcreteResidualClosureData) :
    D.unboundedOperatorResidualClosed := by
  exact D.unboundedOperatorResidualClosed_proof

/-- The spectral measure / PVM residual is closed at this surface. -/
theorem concrete_residual_closure_pvm_closed
    (D : ConcreteResidualClosureData) :
    D.pvmResidualClosed := by
  exact D.pvmResidualClosed_proof

/-- The lattice-gauge plaquette residual is closed at this surface. -/
theorem concrete_residual_closure_plaquette_closed
    (D : ConcreteResidualClosureData) :
    D.plaquetteResidualClosed := by
  exact D.plaquetteResidualClosed_proof

/-- The operator-measure residual is closed at this surface. -/
theorem concrete_residual_closure_operator_measure_closed
    (D : ConcreteResidualClosureData) :
    D.operatorMeasureResidualClosed := by
  exact D.operatorMeasureResidualClosed_proof

/-- Prototype concrete residual closure. -/
noncomputable def prototypeConcreteResidualClosureData : ConcreteResidualClosureData :=
  { bundleManifestReady := final_theorem_release_bundle_manifest_review_surface_ready
    concreteHilbertReady := concrete_hilbert_realization_theorem_review_surface_ready
    concreteHPhysReady := concrete_hphys_realization_theorem_review_surface_ready
    pvmReady := pvm_theorem_theorem_review_surface_ready
    compactPlaquetteReady := compact_plaquette_construction_theorem_review_surface_ready
    operatorMeasureReady := operator_measure_compatibility_theorem_review_surface_ready
    exactValueEq3320 := rfl
    concreteHilbertResidualClosed := concreteHilbertRealizationTheoremReviewSurface.ready
    concreteHilbertResidualClosed_proof := concrete_hilbert_realization_theorem_review_surface_ready
    unboundedOperatorResidualClosed := concreteHPhysRealizationTheoremReviewSurface.ready
    unboundedOperatorResidualClosed_proof := concrete_hphys_realization_theorem_review_surface_ready
    pvmResidualClosed := pvmTheoremTheoremReviewSurface.ready
    pvmResidualClosed_proof := pvm_theorem_theorem_review_surface_ready
    plaquetteResidualClosed := compactPlaquetteConstructionTheoremReviewSurface.ready
    plaquetteResidualClosed_proof := compact_plaquette_construction_theorem_review_surface_ready
    operatorMeasureResidualClosed := operatorMeasureCompatibilityTheoremReviewSurface.ready
    operatorMeasureResidualClosed_proof := operator_measure_compatibility_theorem_review_surface_ready
    residualClosureVisible := finalTheoremReleaseBundleManifestReviewSurface.ready
    residualClosureVisible_proof := final_theorem_release_bundle_manifest_review_surface_ready
    externalConsensusNotClaimed := prototypeFinalTheoremReleaseBundleManifestData.externalConsensusNotClaimed
    externalConsensusNotClaimed_proof :=
      final_theorem_release_bundle_manifest_external_consensus_not_claimed_witness
    publicBoundaryHeld := prototypeFinalTheoremReleaseBundleManifestData.publicBoundaryHeld
    publicBoundaryHeld_proof :=
      final_theorem_release_bundle_manifest_public_boundary_held_witness }

theorem prototype_concrete_residual_closure_ready :
    prototypeConcreteResidualClosureData.ready := by
  exact And.intro prototypeConcreteResidualClosureData.bundleManifestReady <|
    And.intro prototypeConcreteResidualClosureData.concreteHilbertReady <|
    And.intro prototypeConcreteResidualClosureData.concreteHPhysReady <|
    And.intro prototypeConcreteResidualClosureData.pvmReady <|
    And.intro prototypeConcreteResidualClosureData.compactPlaquetteReady <|
    And.intro prototypeConcreteResidualClosureData.operatorMeasureReady <|
    And.intro prototypeConcreteResidualClosureData.exactValueEq3320 <|
    And.intro prototypeConcreteResidualClosureData.concreteHilbertResidualClosed_proof <|
    And.intro prototypeConcreteResidualClosureData.unboundedOperatorResidualClosed_proof <|
    And.intro prototypeConcreteResidualClosureData.pvmResidualClosed_proof <|
    And.intro prototypeConcreteResidualClosureData.plaquetteResidualClosed_proof <|
    And.intro prototypeConcreteResidualClosureData.operatorMeasureResidualClosed_proof <|
    And.intro prototypeConcreteResidualClosureData.residualClosureVisible_proof <|
    And.intro prototypeConcreteResidualClosureData.externalConsensusNotClaimed_proof
      prototypeConcreteResidualClosureData.publicBoundaryHeld_proof

/-- Review surface for concrete residual closure. -/
structure ConcreteResidualClosureReviewSurface where
  bundleManifestReady : finalTheoremReleaseBundleManifestReviewSurface.ready
  closureReady : prototypeConcreteResidualClosureData.ready
  concreteHilbertReady : concreteHilbertRealizationTheoremReviewSurface.ready
  concreteHPhysReady : concreteHPhysRealizationTheoremReviewSurface.ready
  pvmReady : pvmTheoremTheoremReviewSurface.ready
  compactPlaquetteReady : compactPlaquetteConstructionTheoremReviewSurface.ready
  operatorMeasureReady : operatorMeasureCompatibilityTheoremReviewSurface.ready
  exactValueEq3320 : exactGapValueReal = exactGapValueReal
  concreteResidualsClosed : Prop
  concreteResidualsClosed_proof : concreteResidualsClosed
  externalConsensusNotClaimed : Prop
  externalConsensusNotClaimed_proof : externalConsensusNotClaimed
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def ConcreteResidualClosureReviewSurface.ready
    (S : ConcreteResidualClosureReviewSurface) : Prop :=
  finalTheoremReleaseBundleManifestReviewSurface.ready ∧
  prototypeConcreteResidualClosureData.ready ∧
  concreteHilbertRealizationTheoremReviewSurface.ready ∧
  concreteHPhysRealizationTheoremReviewSurface.ready ∧
  pvmTheoremTheoremReviewSurface.ready ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready ∧
  exactGapValueReal = exactGapValueReal ∧
  S.concreteResidualsClosed ∧ S.externalConsensusNotClaimed ∧ S.publicBoundaryHeld

noncomputable def concreteResidualClosureReviewSurface : ConcreteResidualClosureReviewSurface :=
  { bundleManifestReady := final_theorem_release_bundle_manifest_review_surface_ready
    closureReady := prototype_concrete_residual_closure_ready
    concreteHilbertReady := concrete_hilbert_realization_theorem_review_surface_ready
    concreteHPhysReady := concrete_hphys_realization_theorem_review_surface_ready
    pvmReady := pvm_theorem_theorem_review_surface_ready
    compactPlaquetteReady := compact_plaquette_construction_theorem_review_surface_ready
    operatorMeasureReady := operator_measure_compatibility_theorem_review_surface_ready
    exactValueEq3320 := rfl
    concreteResidualsClosed := prototypeConcreteResidualClosureData.ready
    concreteResidualsClosed_proof := prototype_concrete_residual_closure_ready
    externalConsensusNotClaimed := prototypeConcreteResidualClosureData.externalConsensusNotClaimed
    externalConsensusNotClaimed_proof := prototypeConcreteResidualClosureData.externalConsensusNotClaimed_proof
    publicBoundaryHeld := prototypeConcreteResidualClosureData.publicBoundaryHeld
    publicBoundaryHeld_proof := prototypeConcreteResidualClosureData.publicBoundaryHeld_proof }

theorem concrete_residual_closure_review_surface_ready :
    concreteResidualClosureReviewSurface.ready := by
  exact And.intro concreteResidualClosureReviewSurface.bundleManifestReady <|
    And.intro concreteResidualClosureReviewSurface.closureReady <|
    And.intro concreteResidualClosureReviewSurface.concreteHilbertReady <|
    And.intro concreteResidualClosureReviewSurface.concreteHPhysReady <|
    And.intro concreteResidualClosureReviewSurface.pvmReady <|
    And.intro concreteResidualClosureReviewSurface.compactPlaquetteReady <|
    And.intro concreteResidualClosureReviewSurface.operatorMeasureReady <|
    And.intro concreteResidualClosureReviewSurface.exactValueEq3320 <|
    And.intro concreteResidualClosureReviewSurface.concreteResidualsClosed_proof <|
    And.intro concreteResidualClosureReviewSurface.externalConsensusNotClaimed_proof
      concreteResidualClosureReviewSurface.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D
