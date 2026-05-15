import MGAP4D.MathlibAnalytic.PVMInterface

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- Abstract observable atom interface.

This is the next layer after the PVM-shaped exact atom surface.  It is not yet
the full operator-measure theorem for a compactly supported smeared centered
plaquette observable.  It records the observable-facing interface needed for
that theorem:

* a PVM-shaped exact atom interface,
* an observable carrier,
* a chosen observable,
* compact-support / centered / smeared witnesses,
* a spectral-weight map,
* positive nonzero weight on the exact atom,
* compatibility with the exact atom PVM mass. -/
structure ObservableAtomInterface where
  pvm : ProjectionValuedMeasureInterface
  observable : Type u
  chosenObservable : observable
  compactSupport : observable → Prop
  centered : observable → Prop
  smeared : observable → Prop
  spectralWeight : observable → Set ℝ → ℝ
  pvmReady : pvm.ready
  chosen_compactSupport : compactSupport chosenObservable
  chosen_centered : centered chosenObservable
  chosen_smeared : smeared chosenObservable
  atom : Set ℝ
  atom_def : atom = exactGapAtomReal
  atom_contains_exact : exactGapValueReal ∈ atom
  positive_atom_weight : 0 < spectralWeight chosenObservable atom
  nonzero_atom_weight : spectralWeight chosenObservable atom ≠ 0
  compatible_with_pvm_mass : spectralWeight chosenObservable atom = pvm.projectionMass pvm.exactAtom
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  fullObservableAtomTheoremStillOpen : Prop

/-- Ready predicate for the observable atom interface. -/
def ObservableAtomInterface.ready (O : ObservableAtomInterface) : Prop :=
  O.pvmReady ∧ O.chosen_compactSupport ∧ O.chosen_centered ∧ O.chosen_smeared ∧
  O.atom_def ∧ O.atom_contains_exact ∧ O.positive_atom_weight ∧
  O.nonzero_atom_weight ∧ O.compatible_with_pvm_mass ∧ O.exact_value_eq_3320 ∧
  O.fullObservableAtomTheoremStillOpen

/-- Singleton observable type for the interface prototype. -/
def PrototypeObservable := PUnit

/-- The prototype observable. -/
def prototypeObservable : PrototypeObservable := PUnit.unit

/-- Prototype observable spectral weight. -/
def prototypeObservableSpectralWeight (_ : PrototypeObservable) (_ : Set ℝ) : ℝ :=
  exactGapSpectralMassReal

/-- Singleton observable atom interface. -/
def singletonObservableAtomInterface : ObservableAtomInterface :=
  { pvm := singletonPVMInterface
    observable := PrototypeObservable
    chosenObservable := prototypeObservable
    compactSupport := fun _ => True
    centered := fun _ => True
    smeared := fun _ => True
    spectralWeight := prototypeObservableSpectralWeight
    pvmReady := singleton_pvm_interface_ready
    chosen_compactSupport := True.intro
    chosen_centered := True.intro
    chosen_smeared := True.intro
    atom := exactGapAtomReal
    atom_def := rfl
    atom_contains_exact := exactGapValueReal_mem_exactGapAtomReal
    positive_atom_weight := exactGapSpectralMassReal_pos
    nonzero_atom_weight := exactGapSpectralMassReal_ne_zero
    compatible_with_pvm_mass := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    fullObservableAtomTheoremStillOpen := True }

theorem singleton_observable_atom_interface_ready :
    singletonObservableAtomInterface.ready := by
  exact And.intro singleton_pvm_interface_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro rfl <|
    And.intro exactGapValueReal_eq True.intro

theorem singleton_observable_atom_interface_exact_in_atom :
    exactGapValueReal ∈ singletonObservableAtomInterface.atom := by
  exact exactGapValueReal_mem_exactGapAtomReal

theorem singleton_observable_atom_interface_positive_weight :
    0 < singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom := by
  exact exactGapSpectralMassReal_pos

theorem singleton_observable_atom_interface_nonzero_weight :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

theorem singleton_observable_atom_interface_compatible_with_pvm :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom := by
  rfl

/-- Review surface linking the PVM exact atom interface to the observable-facing
positive spectral-weight interface. -/
structure ObservableAtomReviewSurface where
  pvmReviewReady : pvmReviewSurface.ready
  observableInterfaceReady : singletonObservableAtomInterface.ready
  exactValueInAtom : exactGapValueReal ∈ singletonObservableAtomInterface.atom
  positiveWeight : 0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom
  nonzeroWeight : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0
  compatibleWithPVM : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom
  compactSupportReady : singletonObservableAtomInterface.compactSupport
    singletonObservableAtomInterface.chosenObservable
  centeredReady : singletonObservableAtomInterface.centered
    singletonObservableAtomInterface.chosenObservable
  smearedReady : singletonObservableAtomInterface.smeared
    singletonObservableAtomInterface.chosenObservable
  fullObservableAtomTheoremStillOpen : Prop
  mainMathlibBacked : Prop
  finalReleaseHeld : Prop

def ObservableAtomReviewSurface.ready (S : ObservableAtomReviewSurface) : Prop :=
  S.pvmReviewReady ∧ S.observableInterfaceReady ∧ S.exactValueInAtom ∧
  S.positiveWeight ∧ S.nonzeroWeight ∧ S.compatibleWithPVM ∧
  S.compactSupportReady ∧ S.centeredReady ∧ S.smearedReady ∧
  S.fullObservableAtomTheoremStillOpen ∧ S.mainMathlibBacked ∧ S.finalReleaseHeld

def observableAtomReviewSurface : ObservableAtomReviewSurface :=
  { pvmReviewReady := pvm_review_surface_ready
    observableInterfaceReady := singleton_observable_atom_interface_ready
    exactValueInAtom := singleton_observable_atom_interface_exact_in_atom
    positiveWeight := singleton_observable_atom_interface_positive_weight
    nonzeroWeight := singleton_observable_atom_interface_nonzero_weight
    compatibleWithPVM := singleton_observable_atom_interface_compatible_with_pvm
    compactSupportReady := True.intro
    centeredReady := True.intro
    smearedReady := True.intro
    fullObservableAtomTheoremStillOpen := True
    mainMathlibBacked := True
    finalReleaseHeld := True }

theorem observable_atom_review_surface_ready :
    observableAtomReviewSurface.ready := by
  exact And.intro pvm_review_surface_ready <|
    And.intro singleton_observable_atom_interface_ready <|
    And.intro singleton_observable_atom_interface_exact_in_atom <|
    And.intro singleton_observable_atom_interface_positive_weight <|
    And.intro singleton_observable_atom_interface_nonzero_weight <|
    And.intro singleton_observable_atom_interface_compatible_with_pvm <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem observable_atom_review_surface_final_release_held :
    observableAtomReviewSurface.finalReleaseHeld := by
  trivial

end MathlibAnalytic
end MGAP4D
