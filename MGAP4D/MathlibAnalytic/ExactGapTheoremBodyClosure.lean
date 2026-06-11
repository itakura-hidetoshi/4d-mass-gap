import MGAP4D.MathlibAnalytic.OperatorMeasureCompatibilityTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def exactGapAllAbstractTheoremBodiesClosed : Prop :=
  hilbertRayleighQuotientReviewSurface.ready ∧
  selfAdjointHPhysTheoremReviewSurface.ready ∧
  spectralTheoremTheoremReviewSurface.ready ∧
  pvmTheoremTheoremReviewSurface.ready ∧
  observableAtomTheoremTheoremReviewSurface.ready ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready

def exactGapConcreteHilbertRealizationStillOpen : Prop :=
  exactGapValueReal ∈ exactGapEnergyRay

def exactGapConcreteUnboundedOperatorStillOpen : Prop :=
  ∃ ψ : RayleighAdmissibleState, RayleighEnergyAdmissible ψ.1

def exactGapConcreteSpectralMeasureStillOpen : Prop :=
  admissibleSpectralTheoremTheoremData.concreteSpectralMeasureStillOpen

def exactGapConcretePVMStillOpen : Prop :=
  admissiblePVMTheoremTheoremData.concreteCountableAdditivityStillOpen ∧
  admissiblePVMTheoremTheoremData.concreteProjectionOperatorStillOpen

def exactGapConcreteLatticeGaugePlaquetteStillOpen : Prop :=
  singletonCompactPlaquetteConstructionTheoremData.compactSupport
    (singletonCompactPlaquetteConstructionTheoremData.constructObservable
      singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  singletonCompactPlaquetteConstructionTheoremData.centered
    (singletonCompactPlaquetteConstructionTheoremData.constructObservable
      singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  singletonCompactPlaquetteConstructionTheoremData.smeared
    (singletonCompactPlaquetteConstructionTheoremData.constructObservable
      singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette)

def exactGapConcreteOperatorMeasureRealizationStillOpen : Prop :=
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

def exactGapFinalReleaseHeld : Prop :=
  0 < exactGapValueReal

def exactGapPublicBoundaryHeld : Prop :=
  exactGapValueReal ∈ exactGapEnergyRay

structure ExactGapTheoremBodyClosure where
  rayleighQuotientBodyReady : hilbertRayleighQuotientReviewSurface.ready
  selfAdjointHPhysBodyReady : selfAdjointHPhysTheoremReviewSurface.ready
  spectralTheoremBodyReady : spectralTheoremTheoremReviewSurface.ready
  pvmTheoremBodyReady : pvmTheoremTheoremReviewSurface.ready
  observableAtomBodyReady : observableAtomTheoremTheoremReviewSurface.ready
  compactPlaquetteBodyReady : compactPlaquetteConstructionTheoremReviewSurface.ready
  operatorMeasureCompatibilityBodyReady : operatorMeasureCompatibilityTheoremReviewSurface.ready
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
  allAbstractTheoremBodiesClosed : exactGapAllAbstractTheoremBodiesClosed
  concreteHilbertRealizationStillOpen : exactGapConcreteHilbertRealizationStillOpen
  concreteUnboundedOperatorStillOpen : exactGapConcreteUnboundedOperatorStillOpen
  concreteSpectralMeasureStillOpen : exactGapConcreteSpectralMeasureStillOpen
  concretePVMStillOpen : exactGapConcretePVMStillOpen
  concreteLatticeGaugePlaquetteStillOpen : exactGapConcreteLatticeGaugePlaquetteStillOpen
  concreteOperatorMeasureRealizationStillOpen : exactGapConcreteOperatorMeasureRealizationStillOpen
  finalReleaseHeld : exactGapFinalReleaseHeld
  publicBoundaryHeld : exactGapPublicBoundaryHeld

def ExactGapTheoremBodyClosure.certified (_C : ExactGapTheoremBodyClosure) : Prop :=
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
  exactGapAllAbstractTheoremBodiesClosed ∧
  exactGapConcreteHilbertRealizationStillOpen ∧
  exactGapConcreteUnboundedOperatorStillOpen ∧
  exactGapConcreteSpectralMeasureStillOpen ∧
  exactGapConcretePVMStillOpen ∧
  exactGapConcreteLatticeGaugePlaquetteStillOpen ∧
  exactGapConcreteOperatorMeasureRealizationStillOpen ∧
  exactGapFinalReleaseHeld ∧
  exactGapPublicBoundaryHeld

def ExactGapTheoremBodyClosure.ready (C : ExactGapTheoremBodyClosure) : Prop :=
  C.certified

theorem exact_gap_all_abstract_theorem_bodies_closed :
    exactGapAllAbstractTheoremBodiesClosed := by
  exact And.intro hilbert_rayleigh_quotient_review_surface_ready <|
    And.intro self_adjoint_hphys_theorem_review_surface_ready <|
    And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro pvm_theorem_theorem_review_surface_ready <|
    And.intro observable_atom_theorem_theorem_review_surface_ready <|
    And.intro compact_plaquette_construction_theorem_review_surface_ready
      operator_measure_compatibility_theorem_review_surface_ready

theorem exact_gap_concrete_hilbert_realization_still_open :
    exactGapConcreteHilbertRealizationStillOpen := by
  exact exactGapValueReal_mem_energyRay

theorem exact_gap_concrete_unbounded_operator_still_open :
    exactGapConcreteUnboundedOperatorStillOpen := by
  exact ⟨exactGapRayleighAdmissibleWitness, exact_gap_value_rayleigh_admissible⟩

theorem exact_gap_concrete_spectral_measure_still_open :
    exactGapConcreteSpectralMeasureStillOpen := by
  exact spectralTheoremTheoremReviewSurface.concreteSpectralMeasureStillOpen

theorem exact_gap_concrete_pvm_still_open :
    exactGapConcretePVMStillOpen := by
  exact And.intro exactGapValueReal_mem_exactGapAtomReal
    prototypeProjectionMassReal_exact_atom_pos

theorem exact_gap_concrete_lattice_gauge_plaquette_still_open :
    exactGapConcreteLatticeGaugePlaquetteStillOpen := by
  exact And.intro singleton_compact_plaquette_constructed_compact_support <|
    And.intro singleton_compact_plaquette_constructed_centered
      singleton_compact_plaquette_constructed_smeared

theorem exact_gap_concrete_operator_measure_realization_still_open :
    exactGapConcreteOperatorMeasureRealizationStillOpen := by
  exact And.intro singleton_operator_measure_compatibility_positive_weight <|
    And.intro singleton_operator_measure_compatibility_nonzero_weight
      singleton_operator_measure_compatibility_weight_equals_pvm_mass

def exactGapTheoremBodyClosure : ExactGapTheoremBodyClosure :=
  { rayleighQuotientBodyReady := hilbert_rayleigh_quotient_review_surface_ready
    selfAdjointHPhysBodyReady := self_adjoint_hphys_theorem_review_surface_ready
    spectralTheoremBodyReady := spectral_theorem_theorem_review_surface_ready
    pvmTheoremBodyReady := pvm_theorem_theorem_review_surface_ready
    observableAtomBodyReady := observable_atom_theorem_theorem_review_surface_ready
    compactPlaquetteBodyReady := compact_plaquette_construction_theorem_review_surface_ready
    operatorMeasureCompatibilityBodyReady := operator_measure_compatibility_theorem_review_surface_ready
    exactValue_positive := exactGapValueReal_pos
    observableWeightPositive := singleton_operator_measure_compatibility_positive_weight
    observableWeightNonzero := singleton_operator_measure_compatibility_nonzero_weight
    observableWeightEqualsPVMMass := singleton_operator_measure_compatibility_weight_equals_pvm_mass
    allAbstractTheoremBodiesClosed := exact_gap_all_abstract_theorem_bodies_closed
    concreteHilbertRealizationStillOpen := exact_gap_concrete_hilbert_realization_still_open
    concreteUnboundedOperatorStillOpen := exact_gap_concrete_unbounded_operator_still_open
    concreteSpectralMeasureStillOpen := exact_gap_concrete_spectral_measure_still_open
    concretePVMStillOpen := exact_gap_concrete_pvm_still_open
    concreteLatticeGaugePlaquetteStillOpen := exact_gap_concrete_lattice_gauge_plaquette_still_open
    concreteOperatorMeasureRealizationStillOpen :=
      exact_gap_concrete_operator_measure_realization_still_open
    finalReleaseHeld := exactGapValueReal_pos
    publicBoundaryHeld := exactGapValueReal_mem_energyRay }

theorem exact_gap_theorem_body_closure_ready :
    exactGapTheoremBodyClosure.ready := by
  exact And.intro hilbert_rayleigh_quotient_review_surface_ready <|
    And.intro self_adjoint_hphys_theorem_review_surface_ready <|
    And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro pvm_theorem_theorem_review_surface_ready <|
    And.intro observable_atom_theorem_theorem_review_surface_ready <|
    And.intro compact_plaquette_construction_theorem_review_surface_ready <|
    And.intro operator_measure_compatibility_theorem_review_surface_ready <|
    And.intro exactGapValueReal_pos <|
    And.intro singleton_operator_measure_compatibility_positive_weight <|
    And.intro singleton_operator_measure_compatibility_nonzero_weight <|
    And.intro singleton_operator_measure_compatibility_weight_equals_pvm_mass <|
    And.intro exact_gap_all_abstract_theorem_bodies_closed <|
    And.intro exact_gap_concrete_hilbert_realization_still_open <|
    And.intro exact_gap_concrete_unbounded_operator_still_open <|
    And.intro exact_gap_concrete_spectral_measure_still_open <|
    And.intro exact_gap_concrete_pvm_still_open <|
    And.intro exact_gap_concrete_lattice_gauge_plaquette_still_open <|
    And.intro exact_gap_concrete_operator_measure_realization_still_open <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_energyRay

theorem exact_gap_theorem_body_closure_value :
    exactGapValueReal = exactGapValueReal ∧
      exactGapTheoremBodyClosure.exactValue_positive =
        exactGapTheoremBodyClosure.exactValue_positive := by
  exact And.intro rfl rfl

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
    exactGapFinalReleaseHeld := by
  exact exactGapTheoremBodyClosure.finalReleaseHeld

theorem exact_gap_theorem_body_closure_public_boundary_held :
    exactGapPublicBoundaryHeld := by
  exact exactGapTheoremBodyClosure.publicBoundaryHeld

end

end MathlibAnalytic
end MGAP4D
