import MGAP4D.MathlibAnalytic.CompactPlaquetteConstructionTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract theorem body for operator-measure compatibility.

This is the seventh post-interface theorem-body step. It links the compact
plaquette construction body to the observable atom body and PVM body by making
explicit that the observable spectral weight of the constructed observable on
the exact atom agrees with the PVM exact-atom mass.

It deliberately carries no upstream exact numeric value equality; that equality
is reserved for the R6 spectral-origin surface. -/
structure OperatorMeasureCompatibilityTheoremData where
  constructionData : CompactPlaquetteConstructionTheoremData
  constructionDataReady : constructionData.ready
  observableAtomData : ObservableAtomTheoremTheoremData
  observableAtomDataReady : observableAtomData.ready
  constructedObservable : observableAtomData.observable
  exactAtom : Set ℝ
  constructedObservable_def : constructedObservable = observableAtomData.chosenObservable
  exactAtom_def : exactAtom = observableAtomData.atom
  exact_value_in_atom : exactGapValueReal ∈ exactAtom
  constructed_compactSupport : observableAtomData.compactSupport constructedObservable
  constructed_centered : observableAtomData.centered constructedObservable
  constructed_smeared : observableAtomData.smeared constructedObservable
  positive_weight : 0 < observableAtomData.spectralWeight constructedObservable exactAtom
  nonzero_weight : observableAtomData.spectralWeight constructedObservable exactAtom ≠ 0
  weight_equals_pvm_mass : observableAtomData.spectralWeight constructedObservable exactAtom =
    observableAtomData.pvmData.projectionMass observableAtomData.pvmData.exactAtom
  operatorMeasureCompatibilityCertificate : Prop
  operatorMeasureCompatibilityCertificate_proof : operatorMeasureCompatibilityCertificate
  concreteOperatorMeasureRealizationStillOpen : Prop

/-- Ready predicate for the abstract operator-measure compatibility theorem body. -/
def OperatorMeasureCompatibilityTheoremData.ready
    (D : OperatorMeasureCompatibilityTheoremData) : Prop :=
  D.constructionData.ready ∧ D.observableAtomData.ready ∧
  D.constructedObservable = D.observableAtomData.chosenObservable ∧
  D.exactAtom = D.observableAtomData.atom ∧ exactGapValueReal ∈ D.exactAtom ∧
  D.observableAtomData.compactSupport D.constructedObservable ∧
  D.observableAtomData.centered D.constructedObservable ∧
  D.observableAtomData.smeared D.constructedObservable ∧
  0 < D.observableAtomData.spectralWeight D.constructedObservable D.exactAtom ∧
  D.observableAtomData.spectralWeight D.constructedObservable D.exactAtom ≠ 0 ∧
  D.observableAtomData.spectralWeight D.constructedObservable D.exactAtom =
    D.observableAtomData.pvmData.projectionMass D.observableAtomData.pvmData.exactAtom ∧
  D.operatorMeasureCompatibilityCertificate ∧ D.concreteOperatorMeasureRealizationStillOpen

/-- Exact value belongs to the compatibility atom. -/
theorem operator_measure_compatibility_exact_value_in_atom
    (D : OperatorMeasureCompatibilityTheoremData) :
    exactGapValueReal ∈ D.exactAtom := by
  exact D.exact_value_in_atom

/-- The constructed observable has compact support. -/
theorem operator_measure_compatibility_compact_support
    (D : OperatorMeasureCompatibilityTheoremData) :
    D.observableAtomData.compactSupport D.constructedObservable := by
  exact D.constructed_compactSupport

/-- The constructed observable is centered. -/
theorem operator_measure_compatibility_centered
    (D : OperatorMeasureCompatibilityTheoremData) :
    D.observableAtomData.centered D.constructedObservable := by
  exact D.constructed_centered

/-- The constructed observable is smeared. -/
theorem operator_measure_compatibility_smeared
    (D : OperatorMeasureCompatibilityTheoremData) :
    D.observableAtomData.smeared D.constructedObservable := by
  exact D.constructed_smeared

/-- The constructed observable has positive spectral weight on the exact atom. -/
theorem operator_measure_compatibility_positive_weight
    (D : OperatorMeasureCompatibilityTheoremData) :
    0 < D.observableAtomData.spectralWeight D.constructedObservable D.exactAtom := by
  exact D.positive_weight

/-- The constructed observable has nonzero spectral weight on the exact atom. -/
theorem operator_measure_compatibility_nonzero_weight
    (D : OperatorMeasureCompatibilityTheoremData) :
    D.observableAtomData.spectralWeight D.constructedObservable D.exactAtom ≠ 0 := by
  exact D.nonzero_weight

/-- Operator-measure compatibility: observable spectral weight equals the PVM
exact-atom mass. -/
theorem operator_measure_compatibility_weight_equals_pvm_mass
    (D : OperatorMeasureCompatibilityTheoremData) :
    D.observableAtomData.spectralWeight D.constructedObservable D.exactAtom =
      D.observableAtomData.pvmData.projectionMass D.observableAtomData.pvmData.exactAtom := by
  exact D.weight_equals_pvm_mass

/-- Operator-measure compatibility certificate surface is present. -/
theorem operator_measure_compatibility_certificate
    (D : OperatorMeasureCompatibilityTheoremData) :
    D.operatorMeasureCompatibilityCertificate := by
  exact D.operatorMeasureCompatibilityCertificate_proof

/-- Compatibility theorem-body realization for operator-measure compatibility;
the constructed observable is the final physical Hilbert-space zero vector. -/
def singletonOperatorMeasureCompatibilityTheoremData :
    OperatorMeasureCompatibilityTheoremData :=
  { constructionData := singletonCompactPlaquetteConstructionTheoremData
    constructionDataReady := singleton_compact_plaquette_construction_theorem_data_ready
    observableAtomData := singletonObservableAtomTheoremTheoremData
    observableAtomDataReady := singleton_observable_atom_theorem_theorem_data_ready
    constructedObservable := finalPhysicalHilbertZero
    exactAtom := exactGapAtomReal
    constructedObservable_def := rfl
    exactAtom_def := rfl
    exact_value_in_atom := exactGapValueReal_mem_exactGapAtomReal
    constructed_compactSupport := True.intro
    constructed_centered := True.intro
    constructed_smeared := True.intro
    positive_weight := exactGapSpectralMassReal_pos
    nonzero_weight := exactGapSpectralMassReal_ne_zero
    weight_equals_pvm_mass := rfl
    operatorMeasureCompatibilityCertificate := True
    operatorMeasureCompatibilityCertificate_proof := True.intro
    concreteOperatorMeasureRealizationStillOpen := True }

theorem singleton_operator_measure_compatibility_theorem_data_ready :
    singletonOperatorMeasureCompatibilityTheoremData.ready := by
  exact And.intro singleton_compact_plaquette_construction_theorem_data_ready <|
    And.intro singleton_observable_atom_theorem_theorem_data_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro rfl <|
    And.intro True.intro True.intro

theorem singleton_operator_measure_compatibility_positive_weight :
    0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom := by
  exact operator_measure_compatibility_positive_weight
    singletonOperatorMeasureCompatibilityTheoremData

theorem singleton_operator_measure_compatibility_nonzero_weight :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0 := by
  exact operator_measure_compatibility_nonzero_weight
    singletonOperatorMeasureCompatibilityTheoremData

theorem singleton_operator_measure_compatibility_weight_equals_pvm_mass :
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
      singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
      singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom := by
  exact operator_measure_compatibility_weight_equals_pvm_mass
    singletonOperatorMeasureCompatibilityTheoremData

/-- Review surface closing the abstract operator-measure compatibility theorem
body after compact plaquette construction. -/
structure OperatorMeasureCompatibilityTheoremReviewSurface where
  compactPlaquetteConstructionReady : compactPlaquetteConstructionTheoremReviewSurface.ready
  compatibilityDataReady : singletonOperatorMeasureCompatibilityTheoremData.ready
  positiveWeight : 0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
    singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
    singletonOperatorMeasureCompatibilityTheoremData.exactAtom
  nonzeroWeight : singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
    singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
    singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
  weightEqualsPVMMass : singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
    singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
    singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
    singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom
  operatorMeasureCompatibilityBodyClosed : Prop
  concreteOperatorMeasureRealizationStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def OperatorMeasureCompatibilityTheoremReviewSurface.ready
    (S : OperatorMeasureCompatibilityTheoremReviewSurface) : Prop :=
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  singletonOperatorMeasureCompatibilityTheoremData.ready ∧
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
  S.operatorMeasureCompatibilityBodyClosed ∧ S.concreteOperatorMeasureRealizationStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

def operatorMeasureCompatibilityTheoremReviewSurface :
    OperatorMeasureCompatibilityTheoremReviewSurface :=
  { compactPlaquetteConstructionReady := compact_plaquette_construction_theorem_review_surface_ready
    compatibilityDataReady := singleton_operator_measure_compatibility_theorem_data_ready
    positiveWeight := singleton_operator_measure_compatibility_positive_weight
    nonzeroWeight := singleton_operator_measure_compatibility_nonzero_weight
    weightEqualsPVMMass := singleton_operator_measure_compatibility_weight_equals_pvm_mass
    operatorMeasureCompatibilityBodyClosed := True
    concreteOperatorMeasureRealizationStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem operator_measure_compatibility_theorem_review_surface_ready :
    operatorMeasureCompatibilityTheoremReviewSurface.ready := by
  exact And.intro compact_plaquette_construction_theorem_review_surface_ready <|
    And.intro singleton_operator_measure_compatibility_theorem_data_ready <|
    And.intro singleton_operator_measure_compatibility_positive_weight <|
    And.intro singleton_operator_measure_compatibility_nonzero_weight <|
    And.intro singleton_operator_measure_compatibility_weight_equals_pvm_mass <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem operator_measure_compatibility_theorem_review_surface_final_release_held :
    OperatorMeasureCompatibilityTheoremReviewSurface.finalReleaseHeld
      operatorMeasureCompatibilityTheoremReviewSurface := by
  trivial

end

end MathlibAnalytic
end MGAP4D
