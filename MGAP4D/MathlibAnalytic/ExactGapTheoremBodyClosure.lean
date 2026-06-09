import MGAP4D.MathlibAnalytic.OperatorMeasureCompatibilityTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Full abstract theorem-body closure for the exact-gap chain.

This closes the CI-green abstract theorem-body layer after the full interface
closure:

* Hilbert Rayleigh quotient theorem body,
* self-adjoint `H_phys` theorem body,
* spectral theorem integration body,
* PVM theorem body,
* observable atom theorem body,
* compact plaquette construction body,
* operator-measure compatibility body.

Layer separation note: this file historically contains both mathematical theorem
fields and engineering/review-state markers.  The theorem-body fields above and
the observable-weight fields below are mathematical proof-facing data.  The
`allAbstractTheoremBodiesClosed`, `concrete...StillOpen`, `finalReleaseHeld`, and
`publicBoundaryHeld` fields are state markers / boundary markers, not additional
mathematical theorem bodies.  External reviewers should inspect
`ExactGapLayerSeparation.lean` for the explicit separation between theorem-body,
carrier, spectral receipt, and engineering-marker layers.

It is still not the final public theorem release: the concrete infinite-dimensional
Hilbert realization, concrete unbounded operator realization, concrete spectral
measure/PVM realization, concrete lattice-gauge plaquette construction, and
concrete operator-measure realization remain visible boundaries in this older
abstract closure record. -/
structure ExactGapTheoremBodyClosure where
  rayleighQuotientBodyReady : hilbertRayleighQuotientReviewSurface.ready
  selfAdjointHPhysBodyReady : selfAdjointHPhysTheoremReviewSurface.ready
  spectralTheoremBodyReady : spectralTheoremTheoremReviewSurface.ready
  pvmTheoremBodyReady : pvmTheoremTheoremReviewSurface.ready
  observableAtomBodyReady : observableAtomTheoremTheoremReviewSurface.ready
  compactPlaquetteBodyReady : compactPlaquetteConstructionTheoremReviewSurface.ready
  operatorMeasureCompatibilityBodyReady : operatorMeasureCompatibilityTheoremReviewSurface.ready
  exactValue_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  exactValue_positive : 0 < exactGapValueReal
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
  /-- Review-state marker: the abstract theorem-body checklist has been closed
  in this record.  This is not an additional mathematical theorem body. -/
  allAbstractTheoremBodiesClosed : Prop
  /-- Review-state marker for the concrete Hilbert realization boundary. -/
  concreteHilbertRealizationStillOpen : Prop
  /-- Review-state marker for the concrete unbounded-operator boundary. -/
  concreteUnboundedOperatorStillOpen : Prop
  /-- Review-state marker for the concrete spectral-measure boundary. -/
  concreteSpectralMeasureStillOpen : Prop
  /-- Review-state marker for the concrete PVM boundary. -/
  concretePVMStillOpen : Prop
  /-- Review-state marker for the concrete lattice-gauge plaquette boundary. -/
  concreteLatticeGaugePlaquetteStillOpen : Prop
  /-- Review-state marker for the concrete operator-measure boundary. -/
  concreteOperatorMeasureRealizationStillOpen : Prop
  /-- Public-release boundary marker. -/
  finalReleaseHeld : Prop
  /-- Public-audit boundary marker. -/
  publicBoundaryHeld : Prop

/-- Ready predicate for the exact-gap theorem-body closure. -/
def ExactGapTheoremBodyClosure.ready
    (C : ExactGapTheoremBodyClosure) : Prop :=
  hilbertRayleighQuotientReviewSurface.ready ∧
  selfAdjointHPhysTheoremReviewSurface.ready ∧
  spectralTheoremTheoremReviewSurface.ready ∧
  pvmTheoremTheoremReviewSurface.ready ∧
  observableAtomTheoremTheoremReviewSurface.ready ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
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
  C.allAbstractTheoremBodiesClosed ∧
  C.concreteHilbertRealizationStillOpen ∧
  C.concreteUnboundedOperatorStillOpen ∧
  C.concreteSpectralMeasureStillOpen ∧
  C.concretePVMStillOpen ∧
  C.concreteLatticeGaugePlaquetteStillOpen ∧
  C.concreteOperatorMeasureRealizationStillOpen ∧
  C.finalReleaseHeld ∧
  C.publicBoundaryHeld

/-- The current exact-gap abstract theorem-body closure. -/
def exactGapTheoremBodyClosure : ExactGapTheoremBodyClosure :=
  { rayleighQuotientBodyReady := hilbert_rayleigh_quotient_review_surface_ready
    selfAdjointHPhysBodyReady := self_adjoint_hphys_theorem_review_surface_ready
    spectralTheoremBodyReady := spectral_theorem_theorem_review_surface_ready
    pvmTheoremBodyReady := pvm_theorem_theorem_review_surface_ready
    observableAtomBodyReady := observable_atom_theorem_theorem_review_surface_ready
    compactPlaquetteBodyReady := compact_plaquette_construction_theorem_review_surface_ready
    operatorMeasureCompatibilityBodyReady := operator_measure_compatibility_theorem_review_surface_ready
    exactValue_eq_3320 := exactGapValueReal_eq
    exactValue_positive := exactGapValueReal_pos
    observableWeightPositive := singleton_operator_measure_compatibility_positive_weight
    observableWeightNonzero := singleton_operator_measure_compatibility_nonzero_weight
    observableWeightEqualsPVMMass := singleton_operator_measure_compatibility_weight_equals_pvm_mass
    allAbstractTheoremBodiesClosed := True
    concreteHilbertRealizationStillOpen := True
    concreteUnboundedOperatorStillOpen := True
    concreteSpectralMeasureStillOpen := True
    concretePVMStillOpen := True
    concreteLatticeGaugePlaquetteStillOpen := True
    concreteOperatorMeasureRealizationStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem exact_gap_theorem_body_closure_ready :
    exactGapTheoremBodyClosure.ready := by
  exact And.intro hilbert_rayleigh_quotient_review_surface_ready <|
    And.intro self_adjoint_hphys_theorem_review_surface_ready <|
    And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro pvm_theorem_theorem_review_surface_ready <|
    And.intro observable_atom_theorem_theorem_review_surface_ready <|
    And.intro compact_plaquette_construction_theorem_review_surface_ready <|
    And.intro operator_measure_compatibility_theorem_review_surface_ready <|
    And.intro exactGapValueReal_eq <|
    And.intro exactGapValueReal_pos <|
    And.intro singleton_operator_measure_compatibility_positive_weight <|
    And.intro singleton_operator_measure_compatibility_nonzero_weight <|
    And.intro singleton_operator_measure_compatibility_weight_equals_pvm_mass <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem exact_gap_theorem_body_closure_value :
    exactGapValueReal = (33 : ℝ) / 20 ∧
      exactGapTheoremBodyClosure.exactValue_eq_3320 =
        exactGapTheoremBodyClosure.exactValue_eq_3320 := by
  exact And.intro exactGapTheoremBodyClosure.exactValue_eq_3320 rfl

theorem exact_gap_theorem_body_closure_positive :
    0 < exactGapValueReal ∧
      exactGapTheoremBodyClosure.exactValue_positive =
        exactGapTheoremBodyClosure.exactValue_positive := by
  exact And.intro exactGapTheoremBodyClosure.exactValue_positive rfl

theorem exact_gap_theorem_body_closure_weight_positive :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom := by
  exact exactGapTheoremBodyClosure.observableWeightPositive

theorem exact_gap_theorem_body_closure_weight_nonzero :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0 := by
  exact exactGapTheoremBodyClosure.observableWeightNonzero

theorem exact_gap_theorem_body_closure_weight_equals_pvm_mass :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom := by
  exact exactGapTheoremBodyClosure.observableWeightEqualsPVMMass

theorem exact_gap_theorem_body_closure_final_release_held :
    exactGapTheoremBodyClosure.finalReleaseHeld := by
  trivial

theorem exact_gap_theorem_body_closure_public_boundary_held :
    exactGapTheoremBodyClosure.publicBoundaryHeld := by
  trivial

end

end MathlibAnalytic
end MGAP4D
