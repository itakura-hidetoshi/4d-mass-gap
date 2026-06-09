import MGAP4D.MathlibAnalytic.PVMInterface

namespace MGAP4D
namespace MathlibAnalytic

inductive ObservableAtomBoundaryMarker where
  | observableAtomTheoremDeferred
  | mathlibInterfaceBacked
  | finalReleaseHeld
  deriving DecidableEq

structure ObservablePrototypeShell where
  label : String
  exactValue : ℝ
  exactValue_eq_3320 : exactValue = (33 : ℝ) / 20

structure ObservableAtomInterface where
  pvm : ProjectionValuedMeasureInterface
  observable : Type
  chosenObservable : observable
  spectralWeight : observable → Set ℝ → ℝ
  pvmReady : pvm.ready
  atom : Set ℝ
  atom_def : atom = exactGapAtomReal
  atom_contains_exact : exactGapValueReal ∈ atom
  positive_atom_weight : 0 < spectralWeight chosenObservable atom
  nonzero_atom_weight : spectralWeight chosenObservable atom ≠ 0
  compatible_with_pvm_mass : spectralWeight chosenObservable atom = pvm.projectionMass pvm.exactAtom
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  observableAtomBoundary : ObservableAtomBoundaryMarker

def ObservableAtomInterface.ready (O : ObservableAtomInterface) : Prop :=
  O.pvm.ready ∧
  O.atom = exactGapAtomReal ∧
  exactGapValueReal ∈ O.atom ∧
  0 < O.spectralWeight O.chosenObservable O.atom ∧
  O.spectralWeight O.chosenObservable O.atom ≠ 0 ∧
  O.spectralWeight O.chosenObservable O.atom = O.pvm.projectionMass O.pvm.exactAtom ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  O.observableAtomBoundary = ObservableAtomBoundaryMarker.observableAtomTheoremDeferred

def PrototypeObservable := ObservablePrototypeShell

def prototypeObservable : PrototypeObservable :=
  { label := "observable-atom-shell"
    exactValue := (33 : ℝ) / 20
    exactValue_eq_3320 := rfl }

def prototypeObservableSpectralWeight (_ : PrototypeObservable) (_ : Set ℝ) : ℝ :=
  exactGapSpectralMassReal

noncomputable def singletonObservableAtomInterface : ObservableAtomInterface :=
  { pvm := singletonPVMInterface
    observable := PrototypeObservable
    chosenObservable := prototypeObservable
    spectralWeight := prototypeObservableSpectralWeight
    pvmReady := singleton_pvm_interface_ready
    atom := exactGapAtomReal
    atom_def := rfl
    atom_contains_exact := exactGapValueReal_mem_exactGapAtomReal
    positive_atom_weight := exactGapSpectralMassReal_pos
    nonzero_atom_weight := exactGapSpectralMassReal_ne_zero
    compatible_with_pvm_mass := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    observableAtomBoundary := ObservableAtomBoundaryMarker.observableAtomTheoremDeferred }

theorem singleton_observable_atom_interface_ready :
    singletonObservableAtomInterface.ready := by
  exact And.intro singleton_pvm_interface_ready <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro rfl <|
    And.intro exactGapValueReal_eq rfl

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
  observableAtomBoundary : ObservableAtomBoundaryMarker
  mathlibBackedBoundary : ObservableAtomBoundaryMarker
  finalReleaseBoundary : ObservableAtomBoundaryMarker

def ObservableAtomReviewSurface.ready (S : ObservableAtomReviewSurface) : Prop :=
  pvmReviewSurface.ready ∧
  singletonObservableAtomInterface.ready ∧
  exactGapValueReal ∈ singletonObservableAtomInterface.atom ∧
  0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0 ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom ∧
  S.observableAtomBoundary = ObservableAtomBoundaryMarker.observableAtomTheoremDeferred ∧
  S.mathlibBackedBoundary = ObservableAtomBoundaryMarker.mathlibInterfaceBacked ∧
  S.finalReleaseBoundary = ObservableAtomBoundaryMarker.finalReleaseHeld

noncomputable def observableAtomReviewSurface : ObservableAtomReviewSurface :=
  { pvmReviewReady := pvm_review_surface_ready
    observableInterfaceReady := singleton_observable_atom_interface_ready
    exactValueInAtom := singleton_observable_atom_interface_exact_in_atom
    positiveWeight := singleton_observable_atom_interface_positive_weight
    nonzeroWeight := singleton_observable_atom_interface_nonzero_weight
    compatibleWithPVM := singleton_observable_atom_interface_compatible_with_pvm
    observableAtomBoundary := ObservableAtomBoundaryMarker.observableAtomTheoremDeferred
    mathlibBackedBoundary := ObservableAtomBoundaryMarker.mathlibInterfaceBacked
    finalReleaseBoundary := ObservableAtomBoundaryMarker.finalReleaseHeld }

theorem observable_atom_review_surface_ready :
    observableAtomReviewSurface.ready := by
  exact And.intro pvm_review_surface_ready <|
    And.intro singleton_observable_atom_interface_ready <|
    And.intro singleton_observable_atom_interface_exact_in_atom <|
    And.intro singleton_observable_atom_interface_positive_weight <|
    And.intro singleton_observable_atom_interface_nonzero_weight <|
    And.intro singleton_observable_atom_interface_compatible_with_pvm <|
    And.intro rfl <|
    And.intro rfl rfl

theorem observable_atom_review_surface_final_release_held :
    observableAtomReviewSurface.finalReleaseBoundary = ObservableAtomBoundaryMarker.finalReleaseHeld := by
  rfl

end MathlibAnalytic
end MGAP4D
