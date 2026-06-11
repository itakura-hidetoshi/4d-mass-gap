import MGAP4D.MathlibAnalytic.SpectralTheoremInterface

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract projection-valued-measure interface.

This is not yet the full projection-valued-measure theorem.  It records the
next interface layer after spectral support/mass integration: a set-indexed
projection mass surface, with positivity at the exact-gap singleton and
compatibility with the spectral theorem interface.  It carries no upstream
`33/20` equality claim. -/
structure ProjectionValuedMeasureInterface where
  spectral : SpectralTheoremInterface
  projectionMass : Set ℝ → ℝ
  spectralReady : spectral.ready
  exactAtom : Set ℝ
  exactAtom_def : exactAtom = Set.singleton exactGapValueReal
  exact_value_in_atom : exactGapValueReal ∈ exactAtom
  exact_atom_mass_positive : 0 < projectionMass exactAtom
  exact_atom_mass_nonzero : projectionMass exactAtom ≠ 0
  exact_atom_mass_in_positive_ray : projectionMass exactAtom ∈ Set.Ioi (0 : ℝ)

/-- Ready predicate for the abstract PVM interface. -/
def ProjectionValuedMeasureInterface.ready
    (P : ProjectionValuedMeasureInterface) : Prop :=
  P.spectral.ready ∧
  P.exactAtom = Set.singleton exactGapValueReal ∧
  exactGapValueReal ∈ P.exactAtom ∧
  0 < P.projectionMass P.exactAtom ∧
  P.projectionMass P.exactAtom ≠ 0 ∧
  P.projectionMass P.exactAtom ∈ Set.Ioi (0 : ℝ)

/-- Singleton exact-gap atom used by the prototype PVM interface. -/
def exactGapAtomReal : Set ℝ := Set.singleton exactGapValueReal

theorem exactGapValueReal_mem_exactGapAtomReal :
    exactGapValueReal ∈ exactGapAtomReal := by
  change exactGapValueReal ∈ Set.singleton exactGapValueReal
  exact Set.mem_singleton exactGapValueReal

/-- Prototype PVM mass.  It assigns the already-certified positive real mass to
all sets.  This is only an interface witness, not a countably-additive theorem. -/
def prototypeProjectionMassReal (_ : Set ℝ) : ℝ := exactGapSpectralMassReal

theorem prototypeProjectionMassReal_exact_atom_pos :
    0 < prototypeProjectionMassReal exactGapAtomReal := by
  exact exactGapSpectralMassReal_pos

theorem prototypeProjectionMassReal_exact_atom_ne_zero :
    prototypeProjectionMassReal exactGapAtomReal ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

theorem prototypeProjectionMassReal_exact_atom_mem_positive_ray :
    prototypeProjectionMassReal exactGapAtomReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapSpectralMassReal_mem_positive_ray

/-- Singleton PVM interface prototype. -/
noncomputable def singletonPVMInterface : ProjectionValuedMeasureInterface :=
  { spectral := singletonSpectralTheoremInterface
    projectionMass := prototypeProjectionMassReal
    spectralReady := singleton_spectral_theorem_interface_ready
    exactAtom := exactGapAtomReal
    exactAtom_def := rfl
    exact_value_in_atom := exactGapValueReal_mem_exactGapAtomReal
    exact_atom_mass_positive := prototypeProjectionMassReal_exact_atom_pos
    exact_atom_mass_nonzero := prototypeProjectionMassReal_exact_atom_ne_zero
    exact_atom_mass_in_positive_ray := prototypeProjectionMassReal_exact_atom_mem_positive_ray }

theorem singleton_pvm_interface_ready : singletonPVMInterface.ready := by
  exact And.intro singleton_spectral_theorem_interface_ready <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro prototypeProjectionMassReal_exact_atom_pos <|
    And.intro prototypeProjectionMassReal_exact_atom_ne_zero
      prototypeProjectionMassReal_exact_atom_mem_positive_ray

theorem singleton_pvm_interface_exact_value_in_atom :
    exactGapValueReal ∈ singletonPVMInterface.exactAtom := by
  exact exactGapValueReal_mem_exactGapAtomReal

theorem singleton_pvm_interface_exact_atom_mass_positive :
    0 < singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom := by
  exact prototypeProjectionMassReal_exact_atom_pos

theorem singleton_pvm_interface_exact_atom_mass_nonzero :
    singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ≠ 0 := by
  exact prototypeProjectionMassReal_exact_atom_ne_zero

theorem singleton_pvm_interface_exact_atom_mass_in_positive_ray :
    singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ) := by
  exact prototypeProjectionMassReal_exact_atom_mem_positive_ray

/-- Review surface linking spectral theorem integration to the PVM-shaped exact
atom interface. -/
structure PVMReviewSurface where
  spectralReviewReady : spectralTheoremReviewSurface.ready
  pvmInterfaceReady : singletonPVMInterface.ready
  exactValueInAtom : exactGapValueReal ∈ singletonPVMInterface.exactAtom
  exactAtomMassPositive : 0 < singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom
  exactAtomMassNonzero : singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ≠ 0
  exactAtomMassInPositiveRay : singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ)
  exactAtom_def : singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal

def PVMReviewSurface.ready (S : PVMReviewSurface) : Prop :=
  spectralTheoremReviewSurface.ready ∧
  singletonPVMInterface.ready ∧
  exactGapValueReal ∈ singletonPVMInterface.exactAtom ∧
  0 < singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ∧
  singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ≠ 0 ∧
  singletonPVMInterface.projectionMass singletonPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ) ∧
  singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal

noncomputable def pvmReviewSurface : PVMReviewSurface :=
  { spectralReviewReady := spectral_theorem_review_surface_ready
    pvmInterfaceReady := singleton_pvm_interface_ready
    exactValueInAtom := singleton_pvm_interface_exact_value_in_atom
    exactAtomMassPositive := singleton_pvm_interface_exact_atom_mass_positive
    exactAtomMassNonzero := singleton_pvm_interface_exact_atom_mass_nonzero
    exactAtomMassInPositiveRay := singleton_pvm_interface_exact_atom_mass_in_positive_ray
    exactAtom_def := rfl }

theorem pvm_review_surface_ready : pvmReviewSurface.ready := by
  exact And.intro spectral_theorem_review_surface_ready <|
    And.intro singleton_pvm_interface_ready <|
    And.intro singleton_pvm_interface_exact_value_in_atom <|
    And.intro singleton_pvm_interface_exact_atom_mass_positive <|
    And.intro singleton_pvm_interface_exact_atom_mass_nonzero <|
    And.intro singleton_pvm_interface_exact_atom_mass_in_positive_ray rfl

theorem pvm_review_surface_exact_atom_mass_in_positive_ray :
    pvmReviewSurface.exactAtomMassInPositiveRay := by
  exact singleton_pvm_interface_exact_atom_mass_in_positive_ray

end MathlibAnalytic
end MGAP4D
