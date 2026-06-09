import MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure
import MGAP4D.MathlibAnalytic.ContinuumHamiltonianMassGapWitnessProvenance

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathematical theorem-body layer, excluding carrier definitions and engineering
state markers.

This layer contains theorem-body readiness and the observable-weight theorem
facts that come from the abstract theorem-body route.  It deliberately omits
`exactGapValueReal = 33/20` and all `StillOpen` / boundary-marker fields. -/
def ExactGapAbstractTheoremBodyLayerReady : Prop :=
  hilbertRayleighQuotientReviewSurface.ready ∧
  selfAdjointHPhysTheoremReviewSurface.ready ∧
  spectralTheoremTheoremReviewSurface.ready ∧
  pvmTheoremTheoremReviewSurface.ready ∧
  observableAtomTheoremTheoremReviewSurface.ready ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready ∧
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
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom

/-- Carrier layer: the normalized real carrier and its arithmetic checks.

This legacy layer is isolated from the upstream spectral receipt layer; it should
not be read as the source of the R6 exact atom value. -/
def ExactGapCarrierLayerReady : Prop :=
  exactGapValueReal = (33 : ℝ) / 20 ∧
  0 < exactGapValueReal

/-- Proposition extracted from the continuum-Hamiltonian witness provenance map.
This is the proposition proved by
`continuum_hamiltonian_witness_provenance_map_ready`; it is named separately so
that layer separation does not confuse a theorem term with a `Prop`. -/
def ExactGapContinuumWitnessProvenanceLayerReady : Prop :=
  continuumHamiltonianMassGapWitnessData.physicalContinuumHamiltonianReady ∧
    continuumHamiltonianMassGapWitnessData.hphysFromContinuumYMReady ∧
    continuumHamiltonianMassGapWitnessData.selfAdjointSpectralChainReady ∧
    continuumHamiltonianMassGapWitnessData.normalizationToExactGapReady ∧
    continuumHamiltonianMassGapWitnessData.compactCenteredPlaquetteWeightReady ∧
    continuumHamiltonianMassGapWitnessData.spectralMassObservableReady ∧
    continuumHamiltonianMassGapWitnessData.massGapDerivationWitness ∧
    continuumHamiltonianMassGapWitnessData.continuumHamiltonianToMassGapChainReady ∧
    exactGapValueReal = (33 : ℝ) / 20 ∧
    0 < spectralMassRealSurface.mass ∧
    spectralMassRealSurface.mass ≠ 0

/-- Spectral receipt layer.

This layer records the current spectral receipt: the Yang--Mills Hamiltonian
spectral surface, the identification of the normalized carrier with the surface's
`derivedHamiltonianSpectralValue`, and the positive/nonzero spectral-mass facts.
It no longer states that this upstream receipt derives the concrete value
`33/20`; that numeric claim is reserved for the R6 exact-atom layer. -/
def ExactGapSpectralReceiptLayerReady : Prop :=
  yangMillsHamiltonianSpectralDerivation3320.ready ∧
  exactGapValueReal =
    yangMillsHamiltonianSpectralDerivation3320.derivedHamiltonianSpectralValue ∧
  0 < spectralMassRealSurface.mass ∧
  spectralMassRealSurface.mass ≠ 0 ∧
  ExactGapContinuumWitnessProvenanceLayerReady

/-- Engineering/review-marker layer.

This layer isolates the state markers that were historically mixed into closure
records: abstract-body-closed flags, concrete-realization deferred markers, and
public/final boundary markers.  These are review-state markers, not additional
mathematical theorem bodies. -/
def ExactGapEngineeringMarkerLayerReady : Prop :=
  exactGapTheoremBodyClosure.allAbstractTheoremBodiesClosed ∧
  exactGapTheoremBodyClosure.concreteHilbertRealizationStillOpen ∧
  exactGapTheoremBodyClosure.concreteUnboundedOperatorStillOpen ∧
  exactGapTheoremBodyClosure.concreteSpectralMeasureStillOpen ∧
  exactGapTheoremBodyClosure.concretePVMStillOpen ∧
  exactGapTheoremBodyClosure.concreteLatticeGaugePlaquetteStillOpen ∧
  exactGapTheoremBodyClosure.concreteOperatorMeasureRealizationStillOpen ∧
  exactGapTheoremBodyClosure.finalReleaseHeld ∧
  exactGapTheoremBodyClosure.publicBoundaryHeld

/-- The four layers are simultaneously available, while remaining separated for
external review. -/
def ExactGapLayerSeparationReady : Prop :=
  ExactGapAbstractTheoremBodyLayerReady ∧
  ExactGapCarrierLayerReady ∧
  ExactGapSpectralReceiptLayerReady ∧
  ExactGapEngineeringMarkerLayerReady

/-- The abstract theorem-body layer is ready. -/
theorem exact_gap_abstract_theorem_body_layer_ready :
    ExactGapAbstractTheoremBodyLayerReady := by
  exact And.intro hilbert_rayleigh_quotient_review_surface_ready <|
    And.intro self_adjoint_hphys_theorem_review_surface_ready <|
    And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro pvm_theorem_theorem_review_surface_ready <|
    And.intro observable_atom_theorem_theorem_review_surface_ready <|
    And.intro compact_plaquette_construction_theorem_review_surface_ready <|
    And.intro operator_measure_compatibility_theorem_review_surface_ready <|
    And.intro singleton_operator_measure_compatibility_positive_weight <|
    And.intro singleton_operator_measure_compatibility_nonzero_weight
      singleton_operator_measure_compatibility_weight_equals_pvm_mass

/-- The carrier layer is ready. -/
theorem exact_gap_carrier_layer_ready : ExactGapCarrierLayerReady := by
  exact And.intro exactGapValueReal_eq exactGapValueReal_pos

/-- The continuum witness provenance proposition is ready. -/
theorem exact_gap_continuum_witness_provenance_layer_ready :
    ExactGapContinuumWitnessProvenanceLayerReady := by
  exact continuum_hamiltonian_witness_provenance_map_ready

/-- The spectral receipt layer is ready. -/
theorem exact_gap_spectral_receipt_layer_ready :
    ExactGapSpectralReceiptLayerReady := by
  exact And.intro yang_mills_hamiltonian_spectral_derivation_3320_ready <|
    And.intro yang_mills_hamiltonian_exact_gap_eq_spectral_value <|
    And.intro yang_mills_hamiltonian_spectral_derivation_positive_mass <|
    And.intro yang_mills_hamiltonian_spectral_derivation_nonzero_mass
      exact_gap_continuum_witness_provenance_layer_ready

/-- The engineering/review-marker layer is ready. -/
theorem exact_gap_engineering_marker_layer_ready :
    ExactGapEngineeringMarkerLayerReady := by
  unfold ExactGapEngineeringMarkerLayerReady
  repeat constructor <;> trivial

/-- The exact-gap layer separation map is ready. -/
theorem exact_gap_layer_separation_ready : ExactGapLayerSeparationReady := by
  exact And.intro exact_gap_abstract_theorem_body_layer_ready <|
    And.intro exact_gap_carrier_layer_ready <|
    And.intro exact_gap_spectral_receipt_layer_ready
      exact_gap_engineering_marker_layer_ready

/-- Projection: external reviewers can inspect the mathematical theorem-body
layer without consuming carrier definitions or engineering markers. -/
theorem exact_gap_layer_separation_extracts_math_layer
    (h : ExactGapLayerSeparationReady) :
    ExactGapAbstractTheoremBodyLayerReady := by
  exact h.1

/-- Projection: external reviewers can inspect the carrier layer separately. -/
theorem exact_gap_layer_separation_extracts_carrier_layer
    (h : ExactGapLayerSeparationReady) :
    ExactGapCarrierLayerReady := by
  exact h.2.1

/-- Projection: external reviewers can inspect the spectral receipt layer
separately from the carrier layer. -/
theorem exact_gap_layer_separation_extracts_spectral_receipt_layer
    (h : ExactGapLayerSeparationReady) :
    ExactGapSpectralReceiptLayerReady := by
  exact h.2.2.1

/-- Projection: engineering/review markers are isolated from theorem-body and
carrier layers. -/
theorem exact_gap_layer_separation_extracts_marker_layer
    (h : ExactGapLayerSeparationReady) :
    ExactGapEngineeringMarkerLayerReady := by
  exact h.2.2.2

end MathlibAnalytic
end MGAP4D
