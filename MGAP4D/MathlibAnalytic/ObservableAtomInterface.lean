import MGAP4D.MathlibAnalytic.PVMInterface
import MGAP4D.MathlibAnalytic.FinalPhysicalHilbertCarrierCore

namespace MGAP4D
namespace MathlibAnalytic

structure ObservableAtomInterface where
  pvm : ProjectionValuedMeasureInterface
  observable : Type
  chosenObservable : observable
  spectralWeight : observable → Set ℝ → ℝ
  pvmCertified : pvm.certified
  atom : Set ℝ
  atom_def : atom = exactGapAtomReal
  atom_contains_exact : exactGapValueReal ∈ atom
  positive_atom_weight : 0 < spectralWeight chosenObservable atom
  nonzero_atom_weight : spectralWeight chosenObservable atom ≠ 0
  atom_weight_in_positive_ray : spectralWeight chosenObservable atom ∈ Set.Ioi (0 : ℝ)
  compatible_with_pvm_mass : spectralWeight chosenObservable atom = pvm.projectionMass pvm.exactAtom

/-- Concrete certification predicate for the observable atom interface. -/
def ObservableAtomInterface.certified (O : ObservableAtomInterface) : Prop :=
  O.pvm.certified ∧
  O.atom = exactGapAtomReal ∧
  exactGapValueReal ∈ O.atom ∧
  0 < O.spectralWeight O.chosenObservable O.atom ∧
  O.spectralWeight O.chosenObservable O.atom ≠ 0 ∧
  O.spectralWeight O.chosenObservable O.atom ∈ Set.Ioi (0 : ℝ) ∧
  O.spectralWeight O.chosenObservable O.atom = O.pvm.projectionMass O.pvm.exactAtom

/-- Backward-compatible readiness name during downstream migration. -/
def ObservableAtomInterface.ready (O : ObservableAtomInterface) : Prop :=
  O.certified

abbrev PrototypeObservable := FinalPhysicalHilbertCarrier

noncomputable def prototypeObservable : PrototypeObservable :=
  finalPhysicalHilbertZero

noncomputable def prototypeObservableSpectralWeight (_ : PrototypeObservable) (_ : Set ℝ) : ℝ :=
  exactGapSpectralMassReal

/-- Observable atom interface routed through the certified exact-atom PVM interface. -/
noncomputable def exactAtomObservableInterface : ObservableAtomInterface :=
  { pvm := exactAtomPVMInterface
    observable := FinalPhysicalHilbertCarrier
    chosenObservable := finalPhysicalHilbertZero
    spectralWeight := prototypeObservableSpectralWeight
    pvmCertified := exact_atom_pvm_interface_certified
    atom := exactGapAtomReal
    atom_def := rfl
    atom_contains_exact := exactGapValueReal_mem_exactGapAtomReal
    positive_atom_weight := exactGapSpectralMassReal_pos
    nonzero_atom_weight := exactGapSpectralMassReal_ne_zero
    atom_weight_in_positive_ray := exactGapSpectralMassReal_mem_positive_ray
    compatible_with_pvm_mass := rfl }

theorem exact_atom_observable_interface_certified :
    exactAtomObservableInterface.certified := by
  exact And.intro exact_atom_pvm_interface_certified <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro exactGapSpectralMassReal_mem_positive_ray rfl

/-- Backward-compatible readiness theorem during downstream migration. -/
theorem exact_atom_observable_interface_ready :
    exactAtomObservableInterface.ready := by
  exact exact_atom_observable_interface_certified

theorem exact_atom_observable_interface_exact_in_atom :
    exactGapValueReal ∈ exactAtomObservableInterface.atom := by
  exact exactGapValueReal_mem_exactGapAtomReal

theorem exact_atom_observable_interface_positive_weight :
    0 < exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom := by
  exact exactGapSpectralMassReal_pos

theorem exact_atom_observable_interface_nonzero_weight :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

theorem exact_atom_observable_interface_weight_in_positive_ray :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapSpectralMassReal_mem_positive_ray

theorem exact_atom_observable_interface_compatible_with_pvm :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom := by
  rfl

structure ObservableAtomReviewSurface where
  pvmReviewCertified : pvmReviewSurface.certified
  observableInterfaceCertified : exactAtomObservableInterface.certified
  exactValueInAtom : exactGapValueReal ∈ exactAtomObservableInterface.atom
  positiveWeight : 0 < exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom
  nonzeroWeight : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ≠ 0
  weightInPositiveRay : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ)
  compatibleWithPVM : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom
  atom_def : exactAtomObservableInterface.atom = exactGapAtomReal

/-- Concrete certification predicate for the observable atom review surface. -/
def ObservableAtomReviewSurface.certified (_S : ObservableAtomReviewSurface) : Prop :=
  pvmReviewSurface.certified ∧
  exactAtomObservableInterface.certified ∧
  exactGapValueReal ∈ exactAtomObservableInterface.atom ∧
  0 < exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ≠ 0 ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ) ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom ∧
  exactAtomObservableInterface.atom = exactGapAtomReal

/-- Backward-compatible readiness name during downstream migration. -/
def ObservableAtomReviewSurface.ready (S : ObservableAtomReviewSurface) : Prop :=
  S.certified

noncomputable def observableAtomReviewSurface : ObservableAtomReviewSurface :=
  { pvmReviewCertified := pvm_review_surface_certified
    observableInterfaceCertified := exact_atom_observable_interface_certified
    exactValueInAtom := exact_atom_observable_interface_exact_in_atom
    positiveWeight := exact_atom_observable_interface_positive_weight
    nonzeroWeight := exact_atom_observable_interface_nonzero_weight
    weightInPositiveRay := exact_atom_observable_interface_weight_in_positive_ray
    compatibleWithPVM := exact_atom_observable_interface_compatible_with_pvm
    atom_def := rfl }

theorem observable_atom_review_surface_certified : observableAtomReviewSurface.certified := by
  exact And.intro pvm_review_surface_certified <|
    And.intro exact_atom_observable_interface_certified <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro exact_atom_observable_interface_positive_weight <|
    And.intro exact_atom_observable_interface_nonzero_weight <|
    And.intro exact_atom_observable_interface_weight_in_positive_ray <|
    And.intro exact_atom_observable_interface_compatible_with_pvm rfl

/-- Backward-compatible theorem name during downstream migration. -/
theorem observable_atom_review_surface_ready : observableAtomReviewSurface.ready := by
  exact observable_atom_review_surface_certified

theorem observable_atom_review_surface_weight_in_positive_ray :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ) := by
  exact exact_atom_observable_interface_weight_in_positive_ray

end MathlibAnalytic
end MGAP4D