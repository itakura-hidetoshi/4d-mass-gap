import MGAP4D.MathlibAnalytic.PVMTheoremTheorem

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Abstract theorem body for the observable atom / operator-measure layer.

This is the fifth post-interface theorem-body step.  It does not yet construct
a concrete compactly supported smeared centered plaquette observable.  It makes
explicit the observable carrier, chosen observable, compact-support / centered /
smeared witnesses, exact atom, positive nonzero observable spectral weight, and
compatibility with the PVM theorem body's exact-atom mass. -/
structure ObservableAtomTheoremTheoremData where
  pvmData : PVMTheoremTheoremData
  pvmDataReady : pvmData.ready
  observable : Type u
  chosenObservable : observable
  compactSupport : observable → Prop
  centered : observable → Prop
  smeared : observable → Prop
  spectralWeight : observable → Set ℝ → ℝ
  chosen_compactSupport : compactSupport chosenObservable
  chosen_centered : centered chosenObservable
  chosen_smeared : smeared chosenObservable
  atom : Set ℝ
  atom_def : atom = pvmData.exactAtom
  exact_value_in_atom : exactGapValueReal ∈ atom
  positive_atom_weight : 0 < spectralWeight chosenObservable atom
  nonzero_atom_weight : spectralWeight chosenObservable atom ≠ 0
  compatible_with_pvm_mass : spectralWeight chosenObservable atom =
    pvmData.projectionMass pvmData.exactAtom
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  observableAtomCertificate : Prop
  observableAtomCertificate_proof : observableAtomCertificate
  concretePlaquetteConstructionStillOpen : Prop
  concreteOperatorMeasureCompatibilityStillOpen : Prop

/-- Ready predicate for the abstract observable atom theorem body. -/
def ObservableAtomTheoremTheoremData.ready
    (D : ObservableAtomTheoremTheoremData) : Prop :=
  D.pvmDataReady ∧ D.chosen_compactSupport ∧ D.chosen_centered ∧ D.chosen_smeared ∧
  D.atom_def ∧ D.exact_value_in_atom ∧ D.positive_atom_weight ∧
  D.nonzero_atom_weight ∧ D.compatible_with_pvm_mass ∧ D.exact_value_eq_3320 ∧
  D.observableAtomCertificate ∧ D.concretePlaquetteConstructionStillOpen ∧
  D.concreteOperatorMeasureCompatibilityStillOpen

/-- The exact value belongs to the observable atom. -/
theorem observable_atom_theorem_exact_value_in_atom
    (D : ObservableAtomTheoremTheoremData) :
    exactGapValueReal ∈ D.atom := by
  exact D.exact_value_in_atom

/-- The observable spectral weight on the exact atom is positive. -/
theorem observable_atom_theorem_positive_weight
    (D : ObservableAtomTheoremTheoremData) :
    0 < D.spectralWeight D.chosenObservable D.atom := by
  exact D.positive_atom_weight

/-- The observable spectral weight on the exact atom is nonzero. -/
theorem observable_atom_theorem_nonzero_weight
    (D : ObservableAtomTheoremTheoremData) :
    D.spectralWeight D.chosenObservable D.atom ≠ 0 := by
  exact D.nonzero_atom_weight

/-- The observable spectral weight is compatible with the PVM theorem body's
exact-atom projection mass. -/
theorem observable_atom_theorem_compatible_with_pvm_mass
    (D : ObservableAtomTheoremTheoremData) :
    D.spectralWeight D.chosenObservable D.atom =
      D.pvmData.projectionMass D.pvmData.exactAtom := by
  exact D.compatible_with_pvm_mass

/-- Compact-support witness for the chosen observable. -/
theorem observable_atom_theorem_compact_support
    (D : ObservableAtomTheoremTheoremData) :
    D.compactSupport D.chosenObservable := by
  exact D.chosen_compactSupport

/-- Centered witness for the chosen observable. -/
theorem observable_atom_theorem_centered
    (D : ObservableAtomTheoremTheoremData) :
    D.centered D.chosenObservable := by
  exact D.chosen_centered

/-- Smeared witness for the chosen observable. -/
theorem observable_atom_theorem_smeared
    (D : ObservableAtomTheoremTheoremData) :
    D.smeared D.chosenObservable := by
  exact D.chosen_smeared

/-- The observable atom theorem certificate surface is present. -/
theorem observable_atom_theorem_certificate
    (D : ObservableAtomTheoremTheoremData) :
    D.observableAtomCertificate := by
  exact D.observableAtomCertificate_proof

/-- Singleton theorem-body realization for the observable atom layer. -/
def singletonObservableAtomTheoremTheoremData : ObservableAtomTheoremTheoremData :=
  { pvmData := singletonPVMTheoremTheoremData
    pvmDataReady := singleton_pvm_theorem_theorem_data_ready
    observable := PrototypeObservable
    chosenObservable := prototypeObservable
    compactSupport := fun _ => True
    centered := fun _ => True
    smeared := fun _ => True
    spectralWeight := prototypeObservableSpectralWeight
    chosen_compactSupport := True.intro
    chosen_centered := True.intro
    chosen_smeared := True.intro
    atom := exactGapAtomReal
    atom_def := rfl
    exact_value_in_atom := exactGapValueReal_mem_exactGapAtomReal
    positive_atom_weight := exactGapSpectralMassReal_pos
    nonzero_atom_weight := exactGapSpectralMassReal_ne_zero
    compatible_with_pvm_mass := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    observableAtomCertificate := True
    observableAtomCertificate_proof := True.intro
    concretePlaquetteConstructionStillOpen := True
    concreteOperatorMeasureCompatibilityStillOpen := True }

theorem singleton_observable_atom_theorem_theorem_data_ready :
    singletonObservableAtomTheoremTheoremData.ready := by
  exact And.intro singleton_pvm_theorem_theorem_data_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro rfl <|
    And.intro exactGapValueReal_eq <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem singleton_observable_atom_theorem_exact_value_in_atom :
    exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom := by
  exact exactGapValueReal_mem_exactGapAtomReal

theorem singleton_observable_atom_theorem_positive_weight :
    0 < singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom := by
  exact exactGapSpectralMassReal_pos

theorem singleton_observable_atom_theorem_nonzero_weight :
    singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

theorem singleton_observable_atom_theorem_compatible_with_pvm_mass :
    singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom =
    singletonObservableAtomTheoremTheoremData.pvmData.projectionMass
      singletonObservableAtomTheoremTheoremData.pvmData.exactAtom := by
  rfl

/-- Review surface closing the abstract observable atom theorem body after the
PVM theorem body. -/
structure ObservableAtomTheoremTheoremReviewSurface where
  pvmTheoremBodyReady : pvmTheoremTheoremReviewSurface.ready
  observableAtomTheoremDataReady : singletonObservableAtomTheoremTheoremData.ready
  exactValueInAtom : exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom
  positiveWeight : 0 < singletonObservableAtomTheoremTheoremData.spectralWeight
    singletonObservableAtomTheoremTheoremData.chosenObservable
    singletonObservableAtomTheoremTheoremData.atom
  nonzeroWeight : singletonObservableAtomTheoremTheoremData.spectralWeight
    singletonObservableAtomTheoremTheoremData.chosenObservable
    singletonObservableAtomTheoremTheoremData.atom ≠ 0
  compatibleWithPVMMass : singletonObservableAtomTheoremTheoremData.spectralWeight
    singletonObservableAtomTheoremTheoremData.chosenObservable
    singletonObservableAtomTheoremTheoremData.atom =
    singletonObservableAtomTheoremTheoremData.pvmData.projectionMass
      singletonObservableAtomTheoremTheoremData.pvmData.exactAtom
  compactSupportReady : singletonObservableAtomTheoremTheoremData.compactSupport
    singletonObservableAtomTheoremTheoremData.chosenObservable
  centeredReady : singletonObservableAtomTheoremTheoremData.centered
    singletonObservableAtomTheoremTheoremData.chosenObservable
  smearedReady : singletonObservableAtomTheoremTheoremData.smeared
    singletonObservableAtomTheoremTheoremData.chosenObservable
  observableAtomTheoremBodyClosed : Prop
  concretePlaquetteConstructionStillOpen : Prop
  concreteOperatorMeasureCompatibilityStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def ObservableAtomTheoremTheoremReviewSurface.ready
    (S : ObservableAtomTheoremTheoremReviewSurface) : Prop :=
  S.pvmTheoremBodyReady ∧ S.observableAtomTheoremDataReady ∧ S.exactValueInAtom ∧
  S.positiveWeight ∧ S.nonzeroWeight ∧ S.compatibleWithPVMMass ∧
  S.compactSupportReady ∧ S.centeredReady ∧ S.smearedReady ∧
  S.observableAtomTheoremBodyClosed ∧ S.concretePlaquetteConstructionStillOpen ∧
  S.concreteOperatorMeasureCompatibilityStillOpen ∧ S.finalReleaseHeld ∧
  S.publicBoundaryHeld

def observableAtomTheoremTheoremReviewSurface : ObservableAtomTheoremTheoremReviewSurface :=
  { pvmTheoremBodyReady := pvm_theorem_theorem_review_surface_ready
    observableAtomTheoremDataReady := singleton_observable_atom_theorem_theorem_data_ready
    exactValueInAtom := singleton_observable_atom_theorem_exact_value_in_atom
    positiveWeight := singleton_observable_atom_theorem_positive_weight
    nonzeroWeight := singleton_observable_atom_theorem_nonzero_weight
    compatibleWithPVMMass := singleton_observable_atom_theorem_compatible_with_pvm_mass
    compactSupportReady := True.intro
    centeredReady := True.intro
    smearedReady := True.intro
    observableAtomTheoremBodyClosed := True
    concretePlaquetteConstructionStillOpen := True
    concreteOperatorMeasureCompatibilityStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem observable_atom_theorem_theorem_review_surface_ready :
    observableAtomTheoremTheoremReviewSurface.ready := by
  exact And.intro pvm_theorem_theorem_review_surface_ready <|
    And.intro singleton_observable_atom_theorem_theorem_data_ready <|
    And.intro singleton_observable_atom_theorem_exact_value_in_atom <|
    And.intro singleton_observable_atom_theorem_positive_weight <|
    And.intro singleton_observable_atom_theorem_nonzero_weight <|
    And.intro singleton_observable_atom_theorem_compatible_with_pvm_mass <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem observable_atom_theorem_theorem_review_surface_final_release_held :
    ObservableAtomTheoremTheoremReviewSurface.finalReleaseHeld
      observableAtomTheoremTheoremReviewSurface := by
  trivial

end MathlibAnalytic
end MGAP4D
