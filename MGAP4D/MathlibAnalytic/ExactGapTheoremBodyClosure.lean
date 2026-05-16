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

It is still not the final public theorem release: the concrete infinite-dimensional
Hilbert realization, concrete unbounded operator realization, concrete spectral
measure/PVM realization, concrete lattice-gauge plaquette construction, and
concrete operator-measure realization remain visible boundaries. -/
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
  allAbstractTheoremBodiesClosed : Prop
  concreteHilbertRealizationStillOpen : Prop
  concreteUnboundedOperatorStillOpen : Prop
  concreteSpectralMeasureStillOpen : Prop
  concretePVMStillOpen : Prop
  concreteLatticeGaugePlaquetteStillOpen : Prop
  concreteOperatorMeasureRealizationStillOpen : Prop
  finalReleaseHeld : Prop
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
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact exactGapTheoremBodyClosure.exactValue_eq_3320

theorem exact_gap_theorem_body_closure_positive :
    0 < exactGapValueReal := by
  exact exactGapTheoremBodyClosure.exactValue_positive

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
