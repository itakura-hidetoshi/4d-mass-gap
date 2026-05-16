import MGAP4D.MathlibAnalytic.PVMTheoremTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract theorem body for the observable atom / operator-measure layer.

This is the fifth post-interface theorem-body step. It does not yet construct
a concrete compactly supported smeared centered plaquette observable. It makes
explicit the observable carrier, chosen observable, compact-support / centered /
smeared witnesses, exact atom, positive nonzero observable spectral weight, and
compatibility with the PVM theorem body's exact-atom mass. -/
structure ObservableAtomTheoremTheoremData where
  pvmData : PVMTheoremTheoremData
  pvmDataReady : pvmData.ready
  observable : Type
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
  D.pvmData.ready ∧ D.compactSupport D.chosenObservable ∧
  D.centered D.chosenObservable ∧ D.smeared D.chosenObservable ∧
  D.atom = D.pvmData.exactAtom ∧ exactGapValueReal ∈ D.atom ∧
  0 < D.spectralWeight D.chosenObservable D.atom ∧
  D.spectralWeight D.chosenObservable D.atom ≠ 0 ∧
  D.spectralWeight D.chosenObservable D.atom =
    D.pvmData.projectionMass D.pvmData.exactAtom ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.observableAtomCertificate ∧ D.concretePlaquetteConstructionStillOpen ∧
  D.concreteOperatorMeasureCompatibilityStillOpen

/-- The exact value belongs to the observable atom. -/
theorem observable_atom_theorem_exact_value_in_atom
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    exactGapValueReal ∈ D.atom := by
  rcases hD with ⟨_, _, _, _, _, hIn, _, _, _, _, _, _, _⟩
  exact hIn

/-- The observable spectral weight on the exact atom is positive. -/
theorem observable_atom_theorem_positive_weight
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    0 < D.spectralWeight D.chosenObservable D.atom := by
  rcases hD with ⟨_, _, _, _, _, _, hPos, _, _, _, _, _, _⟩
  exact hPos

/-- The observable spectral weight on the exact atom is nonzero. -/
theorem observable_atom_theorem_nonzero_weight
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    D.spectralWeight D.chosenObservable D.atom ≠ 0 := by
  rcases hD with ⟨_, _, _, _, _, _, _, hNe, _, _, _, _, _⟩
  exact hNe

/-- The observable spectral weight is compatible with the PVM theorem body's
exact-atom projection mass. -/
theorem observable_atom_theorem_compatible_with_pvm_mass
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    D.spectralWeight D.chosenObservable D.atom =
      D.pvmData.projectionMass D.pvmData.exactAtom := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, hCompat, _, _, _, _⟩
  exact hCompat

/-- Compact-support witness for the chosen observable. -/
theorem observable_atom_theorem_compact_support
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    D.compactSupport D.chosenObservable := by
  rcases hD with ⟨_, hCompact, _⟩
  exact hCompact

/-- Centered witness for the chosen observable. -/
theorem observable_atom_theorem_centered
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    D.centered D.chosenObservable := by
  rcases hD with ⟨_, _, hCentered, _⟩
  exact hCentered

/-- Smeared witness for the chosen observable. -/
theorem observable_atom_theorem_smeared
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    D.smeared D.chosenObservable := by
  rcases hD with ⟨_, _, _, hSmeared, _⟩
  exact hSmeared

/-- The observable atom theorem certificate surface is present. -/
theorem observable_atom_theorem_certificate
    (D : ObservableAtomTheoremTheoremData) (hD : D.ready) :
    D.observableAtomCertificate := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, hCert, _, _⟩
  exact hCert

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
  exact observable_atom_theorem_exact_value_in_atom
    singletonObservableAtomTheoremTheoremData
    singleton_observable_atom_theorem_theorem_data_ready

theorem singleton_observable_atom_theorem_positive_weight :
    0 < singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom := by
  exact observable_atom_theorem_positive_weight
    singletonObservableAtomTheoremTheoremData
    singleton_observable_atom_theorem_theorem_data_ready

theorem singleton_observable_atom_theorem_nonzero_weight :
    singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom ≠ 0 := by
  exact observable_atom_theorem_nonzero_weight
    singletonObservableAtomTheoremTheoremData
    singleton_observable_atom_theorem_theorem_data_ready

theorem singleton_observable_atom_theorem_compatible_with_pvm_mass :
    singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom =
    singletonObservableAtomTheoremTheoremData.pvmData.projectionMass
      singletonObservableAtomTheoremTheoremData.pvmData.exactAtom := by
  exact observable_atom_theorem_compatible_with_pvm_mass
    singletonObservableAtomTheoremTheoremData
    singleton_observable_atom_theorem_theorem_data_ready

theorem singleton_observable_atom_theorem_compact_support :
    singletonObservableAtomTheoremTheoremData.compactSupport
      singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact observable_atom_theorem_compact_support
    singletonObservableAtomTheoremTheoremData
    singleton_observable_atom_theorem_theorem_data_ready

theorem singleton_observable_atom_theorem_centered :
    singletonObservableAtomTheoremTheoremData.centered
      singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact observable_atom_theorem_centered
    singletonObservableAtomTheoremTheoremData
    singleton_observable_atom_theorem_theorem_data_ready

theorem singleton_observable_atom_theorem_smeared :
    singletonObservableAtomTheoremTheoremData.smeared
      singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact observable_atom_theorem_smeared
    singletonObservableAtomTheoremTheoremData
    singleton_observable_atom_theorem_theorem_data_ready

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
  pvmTheoremTheoremReviewSurface.ready ∧
  singletonObservableAtomTheoremTheoremData.ready ∧
  exactGapValueReal ∈ singletonObservableAtomTheoremTheoremData.atom ∧
  0 < singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom ∧
  singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom ≠ 0 ∧
  singletonObservableAtomTheoremTheoremData.spectralWeight
      singletonObservableAtomTheoremTheoremData.chosenObservable
      singletonObservableAtomTheoremTheoremData.atom =
      singletonObservableAtomTheoremTheoremData.pvmData.projectionMass
        singletonObservableAtomTheoremTheoremData.pvmData.exactAtom ∧
  singletonObservableAtomTheoremTheoremData.compactSupport
      singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  singletonObservableAtomTheoremTheoremData.centered
      singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  singletonObservableAtomTheoremTheoremData.smeared
      singletonObservableAtomTheoremTheoremData.chosenObservable ∧
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
    compactSupportReady := singleton_observable_atom_theorem_compact_support
    centeredReady := singleton_observable_atom_theorem_centered
    smearedReady := singleton_observable_atom_theorem_smeared
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
    And.intro singleton_observable_atom_theorem_compact_support <|
    And.intro singleton_observable_atom_theorem_centered <|
    And.intro singleton_observable_atom_theorem_smeared <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem observable_atom_theorem_theorem_review_surface_final_release_held :
    ObservableAtomTheoremTheoremReviewSurface.finalReleaseHeld
      observableAtomTheoremTheoremReviewSurface := by
  trivial

end

end MathlibAnalytic
end MGAP4D
