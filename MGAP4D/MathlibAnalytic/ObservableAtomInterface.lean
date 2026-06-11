import MGAP4D.MathlibAnalytic.PVMInterface
import MGAP4D.MathlibAnalytic.FinalPhysicalHilbertCarrierCore

namespace MGAP4D
namespace MathlibAnalytic

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
  atom_weight_in_positive_ray : spectralWeight chosenObservable atom ∈ Set.Ioi (0 : ℝ)
  compatible_with_pvm_mass : spectralWeight chosenObservable atom = pvm.projectionMass pvm.exactAtom

def ObservableAtomInterface.ready (O : ObservableAtomInterface) : Prop :=
  O.pvm.ready ∧
  O.atom = exactGapAtomReal ∧
  exactGapValueReal ∈ O.atom ∧
  0 < O.spectralWeight O.chosenObservable O.atom ∧
  O.spectralWeight O.chosenObservable O.atom ≠ 0 ∧
  O.spectralWeight O.chosenObservable O.atom ∈ Set.Ioi (0 : ℝ) ∧
  O.spectralWeight O.chosenObservable O.atom = O.pvm.projectionMass O.pvm.exactAtom

abbrev PrototypeObservable := FinalPhysicalHilbertCarrier

noncomputable def prototypeObservable : PrototypeObservable :=
  finalPhysicalHilbertZero

noncomputable def prototypeObservableSpectralWeight (_ : PrototypeObservable) (_ : Set ℝ) : ℝ :=
  exactGapSpectralMassReal

noncomputable def singletonObservableAtomInterface : ObservableAtomInterface :=
  { pvm := singletonPVMInterface
    observable := FinalPhysicalHilbertCarrier
    chosenObservable := finalPhysicalHilbertZero
    spectralWeight := prototypeObservableSpectralWeight
    pvmReady := singleton_pvm_interface_ready
    atom := exactGapAtomReal
    atom_def := rfl
    atom_contains_exact := exactGapValueReal_mem_exactGapAtomReal
    positive_atom_weight := exactGapSpectralMassReal_pos
    nonzero_atom_weight := exactGapSpectralMassReal_ne_zero
    atom_weight_in_positive_ray := exactGapSpectralMassReal_mem_positive_ray
    compatible_with_pvm_mass := rfl }

theorem singleton_observable_atom_interface_ready :
    singletonObservableAtomInterface.ready := by
  exact And.intro singleton_pvm_interface_ready <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro exactGapSpectralMassReal_mem_positive_ray rfl

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

theorem singleton_observable_atom_interface_weight_in_positive_ray :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapSpectralMassReal_mem_positive_ray

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
  weightInPositiveRay : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ)
  compatibleWithPVM : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom
  atom_def : singletonObservableAtomInterface.atom = exactGapAtomReal

def ObservableAtomReviewSurface.ready (_S : ObservableAtomReviewSurface) : Prop :=
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
    singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ) ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom ∧
  singletonObservableAtomInterface.atom = exactGapAtomReal

noncomputable def observableAtomReviewSurface : ObservableAtomReviewSurface :=
  { pvmReviewReady := pvm_review_surface_ready
    observableInterfaceReady := singleton_observable_atom_interface_ready
    exactValueInAtom := singleton_observable_atom_interface_exact_in_atom
    positiveWeight := singleton_observable_atom_interface_positive_weight
    nonzeroWeight := singleton_observable_atom_interface_nonzero_weight
    weightInPositiveRay := singleton_observable_atom_interface_weight_in_positive_ray
    compatibleWithPVM := singleton_observable_atom_interface_compatible_with_pvm
    atom_def := rfl }

theorem observable_atom_review_surface_ready : observableAtomReviewSurface.ready := by
  exact And.intro pvm_review_surface_ready <|
    And.intro singleton_observable_atom_interface_ready <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro singleton_observable_atom_interface_positive_weight <|
    And.intro singleton_observable_atom_interface_nonzero_weight <|
    And.intro singleton_observable_atom_interface_weight_in_positive_ray <|
    And.intro singleton_observable_atom_interface_compatible_with_pvm rfl

theorem observable_atom_review_surface_weight_in_positive_ray :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ) := by
  exact singleton_observable_atom_interface_weight_in_positive_ray

end MathlibAnalytic
end MGAP4D
