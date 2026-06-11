import MGAP4D.MathlibAnalytic.SpectralTheoremInterface

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract projection-valued-measure interface.

This is not yet the full projection-valued-measure theorem.  It records the
next interface layer after spectral support/mass integration: a set-indexed
projection mass surface, with positivity at the exact-gap atom and
compatibility with the spectral theorem interface.  It carries no upstream
`33/20` equality claim. -/
structure ProjectionValuedMeasureInterface where
  spectral : SpectralTheoremInterface
  projectionMass : Set ℝ → ℝ
  spectralCertified : spectral.certified
  exactAtom : Set ℝ
  exactAtom_def : exactAtom = Set.singleton exactGapValueReal
  exact_value_in_atom : exactGapValueReal ∈ exactAtom
  exact_atom_mass_positive : 0 < projectionMass exactAtom
  exact_atom_mass_nonzero : projectionMass exactAtom ≠ 0
  exact_atom_mass_in_positive_ray : projectionMass exactAtom ∈ Set.Ioi (0 : ℝ)

/-- Concrete certification predicate for the abstract PVM interface. -/
def ProjectionValuedMeasureInterface.certified
    (P : ProjectionValuedMeasureInterface) : Prop :=
  P.spectral.certified ∧
  P.exactAtom = Set.singleton exactGapValueReal ∧
  exactGapValueReal ∈ P.exactAtom ∧
  0 < P.projectionMass P.exactAtom ∧
  P.projectionMass P.exactAtom ≠ 0 ∧
  P.projectionMass P.exactAtom ∈ Set.Ioi (0 : ℝ)

/-- Backward-compatible readiness name during downstream migration. -/
def ProjectionValuedMeasureInterface.ready
    (P : ProjectionValuedMeasureInterface) : Prop :=
  P.certified

/-- Exact-gap spectral atom used by the PVM interface. -/
def exactGapAtomReal : Set ℝ := Set.singleton exactGapValueReal

theorem exactGapValueReal_mem_exactGapAtomReal :
    exactGapValueReal ∈ exactGapAtomReal := by
  change exactGapValueReal ∈ Set.singleton exactGapValueReal
  exact Set.mem_singleton exactGapValueReal

/-- Interface PVM mass.  It assigns the already-certified positive real mass to
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

/-- PVM interface routed through the certified admissible spectral interface. -/
noncomputable def exactAtomPVMInterface : ProjectionValuedMeasureInterface :=
  { spectral := admissibleSpectralTheoremInterface
    projectionMass := prototypeProjectionMassReal
    spectralCertified := admissible_spectral_theorem_interface_certified
    exactAtom := exactGapAtomReal
    exactAtom_def := rfl
    exact_value_in_atom := exactGapValueReal_mem_exactGapAtomReal
    exact_atom_mass_positive := prototypeProjectionMassReal_exact_atom_pos
    exact_atom_mass_nonzero := prototypeProjectionMassReal_exact_atom_ne_zero
    exact_atom_mass_in_positive_ray := prototypeProjectionMassReal_exact_atom_mem_positive_ray }

theorem exact_atom_pvm_interface_certified : exactAtomPVMInterface.certified := by
  exact And.intro admissible_spectral_theorem_interface_certified <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro prototypeProjectionMassReal_exact_atom_pos <|
    And.intro prototypeProjectionMassReal_exact_atom_ne_zero
      prototypeProjectionMassReal_exact_atom_mem_positive_ray

/-- Backward-compatible readiness theorem during downstream migration. -/
theorem exact_atom_pvm_interface_ready : exactAtomPVMInterface.ready := by
  exact exact_atom_pvm_interface_certified

theorem exact_atom_pvm_interface_exact_value_in_atom :
    exactGapValueReal ∈ exactAtomPVMInterface.exactAtom := by
  exact exactGapValueReal_mem_exactGapAtomReal

theorem exact_atom_pvm_interface_exact_atom_mass_positive :
    0 < exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom := by
  exact prototypeProjectionMassReal_exact_atom_pos

theorem exact_atom_pvm_interface_exact_atom_mass_nonzero :
    exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ≠ 0 := by
  exact prototypeProjectionMassReal_exact_atom_ne_zero

theorem exact_atom_pvm_interface_exact_atom_mass_in_positive_ray :
    exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ) := by
  exact prototypeProjectionMassReal_exact_atom_mem_positive_ray

/-- Review surface linking spectral theorem integration to the PVM-shaped exact
atom interface. -/
structure PVMReviewSurface where
  spectralReviewCertified : spectralTheoremReviewSurface.certified
  pvmInterfaceCertified : exactAtomPVMInterface.certified
  exactValueInAtom : exactGapValueReal ∈ exactAtomPVMInterface.exactAtom
  exactAtomMassPositive : 0 < exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom
  exactAtomMassNonzero : exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ≠ 0
  exactAtomMassInPositiveRay : exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ)
  exactAtom_def : exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal

/-- Concrete certification predicate for the PVM review surface. -/
def PVMReviewSurface.certified (_S : PVMReviewSurface) : Prop :=
  spectralTheoremReviewSurface.certified ∧
  exactAtomPVMInterface.certified ∧
  exactGapValueReal ∈ exactAtomPVMInterface.exactAtom ∧
  0 < exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∧
  exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ≠ 0 ∧
  exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ) ∧
  exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal

/-- Backward-compatible readiness name during downstream migration. -/
def PVMReviewSurface.ready (S : PVMReviewSurface) : Prop :=
  S.certified

noncomputable def pvmReviewSurface : PVMReviewSurface :=
  { spectralReviewCertified := spectral_theorem_review_surface_certified
    pvmInterfaceCertified := exact_atom_pvm_interface_certified
    exactValueInAtom := exact_atom_pvm_interface_exact_value_in_atom
    exactAtomMassPositive := exact_atom_pvm_interface_exact_atom_mass_positive
    exactAtomMassNonzero := exact_atom_pvm_interface_exact_atom_mass_nonzero
    exactAtomMassInPositiveRay := exact_atom_pvm_interface_exact_atom_mass_in_positive_ray
    exactAtom_def := rfl }

theorem pvm_review_surface_certified : pvmReviewSurface.certified := by
  exact And.intro spectral_theorem_review_surface_certified <|
    And.intro exact_atom_pvm_interface_certified <|
    And.intro exact_atom_pvm_interface_exact_value_in_atom <|
    And.intro exact_atom_pvm_interface_exact_atom_mass_positive <|
    And.intro exact_atom_pvm_interface_exact_atom_mass_nonzero <|
    And.intro exact_atom_pvm_interface_exact_atom_mass_in_positive_ray rfl

/-- Backward-compatible theorem name during downstream migration. -/
theorem pvm_review_surface_ready : pvmReviewSurface.ready := by
  exact pvm_review_surface_certified

theorem pvm_review_surface_exact_atom_mass_in_positive_ray :
    exactAtomPVMInterface.projectionMass exactAtomPVMInterface.exactAtom ∈ Set.Ioi (0 : ℝ) := by
  exact exact_atom_pvm_interface_exact_atom_mass_in_positive_ray

end MathlibAnalytic
end MGAP4D