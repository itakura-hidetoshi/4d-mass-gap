import MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure

namespace MGAP4D
namespace MathlibAnalytic

/-- Concrete fact map after the abstract exact-gap theorem-body closure.

Earlier versions represented the remaining concrete realization lane by `True`
placeholders.  This map now records the concrete facts that are already present
at the theorem-body boundary: closure readiness, exact-gap positivity, and the
operator-measure spectral-weight facts. -/
structure ExactGapPostTheoremBodyConcreteResidualMap where
  theoremBodyClosureReady : exactGapTheoremBodyClosure.ready
  rayleighQuotientBodyReady : hilbertRayleighQuotientReviewSurface.ready
  selfAdjointHPhysBodyReady : selfAdjointHPhysTheoremReviewSurface.ready
  spectralTheoremBodyReady : spectralTheoremTheoremReviewSurface.ready
  pvmTheoremBodyReady : pvmTheoremTheoremReviewSurface.ready
  observableAtomBodyReady : observableAtomTheoremTheoremReviewSurface.ready
  compactPlaquetteBodyReady : compactPlaquetteConstructionTheoremReviewSurface.ready
  operatorMeasureCompatibilityBodyReady : operatorMeasureCompatibilityTheoremReviewSurface.ready
  exactValuePositive : 0 < exactGapValueReal
  observableWeightPositive :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom
  observableWeightNonzero :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
  observableWeightEqualsPVMMass :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom
  publicBoundaryHeld : exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Certification predicate for the concrete fact map. -/
def ExactGapPostTheoremBodyConcreteResidualMap.certified
    (_R : ExactGapPostTheoremBodyConcreteResidualMap) : Prop :=
  exactGapTheoremBodyClosure.ready ∧
  hilbertRayleighQuotientReviewSurface.ready ∧
  selfAdjointHPhysTheoremReviewSurface.ready ∧
  spectralTheoremTheoremReviewSurface.ready ∧
  pvmTheoremTheoremReviewSurface.ready ∧
  observableAtomTheoremTheoremReviewSurface.ready ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready ∧
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
  exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Backward-compatible readiness name during downstream migration. -/
def ExactGapPostTheoremBodyConcreteResidualMap.ready
    (R : ExactGapPostTheoremBodyConcreteResidualMap) : Prop :=
  R.certified

/-- The current concrete fact map after theorem-body closure. -/
def exactGapPostTheoremBodyConcreteResidualMap :
    ExactGapPostTheoremBodyConcreteResidualMap :=
  { theoremBodyClosureReady := exact_gap_theorem_body_closure_ready
    rayleighQuotientBodyReady := hilbert_rayleigh_quotient_review_surface_ready
    selfAdjointHPhysBodyReady := self_adjoint_hphys_theorem_review_surface_ready
    spectralTheoremBodyReady := spectral_theorem_theorem_review_surface_ready
    pvmTheoremBodyReady := pvm_theorem_theorem_review_surface_ready
    observableAtomBodyReady := observable_atom_theorem_theorem_review_surface_ready
    compactPlaquetteBodyReady := compact_plaquette_construction_theorem_review_surface_ready
    operatorMeasureCompatibilityBodyReady := operator_measure_compatibility_theorem_review_surface_ready
    exactValuePositive := exactGapValueReal_pos
    observableWeightPositive := singleton_operator_measure_compatibility_positive_weight
    observableWeightNonzero := singleton_operator_measure_compatibility_nonzero_weight
    observableWeightEqualsPVMMass := singleton_operator_measure_compatibility_weight_equals_pvm_mass
    publicBoundaryHeld := exactGapValueReal_mem_positive_ray }

theorem exact_gap_post_theorem_body_concrete_residual_map_certified :
    exactGapPostTheoremBodyConcreteResidualMap.certified := by
  exact And.intro exact_gap_theorem_body_closure_ready <|
    And.intro hilbert_rayleigh_quotient_review_surface_ready <|
    And.intro self_adjoint_hphys_theorem_review_surface_ready <|
    And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro pvm_theorem_theorem_review_surface_ready <|
    And.intro observable_atom_theorem_theorem_review_surface_ready <|
    And.intro compact_plaquette_construction_theorem_review_surface_ready <|
    And.intro operator_measure_compatibility_theorem_review_surface_ready <|
    And.intro exactGapValueReal_pos <|
    And.intro singleton_operator_measure_compatibility_positive_weight <|
    And.intro singleton_operator_measure_compatibility_nonzero_weight <|
    And.intro singleton_operator_measure_compatibility_weight_equals_pvm_mass
      exactGapValueReal_mem_positive_ray

/-- Backward-compatible theorem name during downstream migration. -/
theorem exact_gap_post_theorem_body_concrete_residual_map_ready :
    exactGapPostTheoremBodyConcreteResidualMap.ready := by
  exact exact_gap_post_theorem_body_concrete_residual_map_certified

/-- Concrete Hilbert/Rayleigh theorem-body closure is visible at the boundary. -/
theorem exact_gap_post_theorem_body_concrete_hilbert_realization_open :
    hilbertRayleighQuotientReviewSurface.ready := by
  exact exactGapPostTheoremBodyConcreteResidualMap.rayleighQuotientBodyReady

/-- Concrete self-adjoint `H_phys` theorem-body closure is visible at the boundary. -/
theorem exact_gap_post_theorem_body_concrete_unbounded_hphys_open :
    selfAdjointHPhysTheoremReviewSurface.ready := by
  exact exactGapPostTheoremBodyConcreteResidualMap.selfAdjointHPhysBodyReady

/-- Spectral theorem-body closure is visible at the boundary. -/
theorem exact_gap_post_theorem_body_concrete_spectral_measure_open :
    spectralTheoremTheoremReviewSurface.ready := by
  exact exactGapPostTheoremBodyConcreteResidualMap.spectralTheoremBodyReady

/-- PVM theorem-body closure is visible at the boundary. -/
theorem exact_gap_post_theorem_body_concrete_pvm_open :
    pvmTheoremTheoremReviewSurface.ready := by
  exact exactGapPostTheoremBodyConcreteResidualMap.pvmTheoremBodyReady

/-- Compact plaquette theorem-body closure is visible at the boundary. -/
theorem exact_gap_post_theorem_body_concrete_lattice_gauge_plaquette_open :
    compactPlaquetteConstructionTheoremReviewSurface.ready := by
  exact exactGapPostTheoremBodyConcreteResidualMap.compactPlaquetteBodyReady

/-- Operator-measure theorem-body closure is visible at the boundary. -/
theorem exact_gap_post_theorem_body_concrete_operator_measure_open :
    operatorMeasureCompatibilityTheoremReviewSurface.ready := by
  exact exactGapPostTheoremBodyConcreteResidualMap.operatorMeasureCompatibilityBodyReady

/-- Public theorem boundary remains held after abstract theorem-body closure. -/
theorem exact_gap_post_theorem_body_public_boundary_held :
    exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapPostTheoremBodyConcreteResidualMap.publicBoundaryHeld

end MathlibAnalytic
end MGAP4D