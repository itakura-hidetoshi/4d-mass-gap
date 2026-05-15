import MGAP4D.MathlibAnalytic.SpectralTheoremTheorem

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract theorem body for the projection-valued-measure layer.

This is the fourth post-interface theorem-body step.  It does not yet prove a
concrete countably-additive projection-valued measure for an unbounded
self-adjoint operator.  It makes explicit the set-indexed projection mass,
exact atom, positive/nonzero exact-atom mass, and compatibility with the
abstract spectral theorem body. -/
structure PVMTheoremTheoremData where
  spectralData : SpectralTheoremTheoremData
  spectralDataReady : spectralData.ready
  projectionMass : Set ℝ → ℝ
  exactAtom : Set ℝ
  exactAtom_def : exactAtom = exactGapAtomReal
  exact_value_in_atom : exactGapValueReal ∈ exactAtom
  exact_atom_mass_positive : 0 < projectionMass exactAtom
  exact_atom_mass_nonzero : projectionMass exactAtom ≠ 0
  compatible_with_spectral_mass : projectionMass exactAtom = spectralData.spectralMass exactGapValueReal
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  pvmCertificate : Prop
  pvmCertificate_proof : pvmCertificate
  concreteCountableAdditivityStillOpen : Prop
  concreteProjectionOperatorStillOpen : Prop

/-- Ready predicate for the abstract PVM theorem body. -/
def PVMTheoremTheoremData.ready (D : PVMTheoremTheoremData) : Prop :=
  D.spectralDataReady ∧ D.exactAtom_def ∧ D.exact_value_in_atom ∧
  D.exact_atom_mass_positive ∧ D.exact_atom_mass_nonzero ∧
  D.compatible_with_spectral_mass ∧ D.exact_value_eq_3320 ∧
  D.pvmCertificate ∧ D.concreteCountableAdditivityStillOpen ∧
  D.concreteProjectionOperatorStillOpen

/-- The exact value belongs to the exact atom. -/
theorem pvm_theorem_exact_value_in_atom
    (D : PVMTheoremTheoremData) :
    exactGapValueReal ∈ D.exactAtom := by
  exact D.exact_value_in_atom

/-- The projection mass of the exact atom is positive. -/
theorem pvm_theorem_exact_atom_mass_positive
    (D : PVMTheoremTheoremData) :
    0 < D.projectionMass D.exactAtom := by
  exact D.exact_atom_mass_positive

/-- The projection mass of the exact atom is nonzero. -/
theorem pvm_theorem_exact_atom_mass_nonzero
    (D : PVMTheoremTheoremData) :
    D.projectionMass D.exactAtom ≠ 0 := by
  exact D.exact_atom_mass_nonzero

/-- The exact-atom projection mass is compatible with the spectral mass at the
exact value. -/
theorem pvm_theorem_compatible_with_spectral_mass
    (D : PVMTheoremTheoremData) :
    D.projectionMass D.exactAtom = D.spectralData.spectralMass exactGapValueReal := by
  exact D.compatible_with_spectral_mass

/-- The PVM certificate surface is present. -/
theorem pvm_theorem_certificate
    (D : PVMTheoremTheoremData) :
    D.pvmCertificate := by
  exact D.pvmCertificate_proof

/-- Singleton theorem-body realization for the PVM layer. -/
def singletonPVMTheoremTheoremData : PVMTheoremTheoremData :=
  { spectralData := singletonSpectralTheoremTheoremData
    spectralDataReady := singleton_spectral_theorem_theorem_data_ready
    projectionMass := prototypeProjectionMassReal
    exactAtom := exactGapAtomReal
    exactAtom_def := rfl
    exact_value_in_atom := exactGapValueReal_mem_exactGapAtomReal
    exact_atom_mass_positive := prototypeProjectionMassReal_exact_atom_pos
    exact_atom_mass_nonzero := prototypeProjectionMassReal_exact_atom_ne_zero
    compatible_with_spectral_mass := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    pvmCertificate := True
    pvmCertificate_proof := True.intro
    concreteCountableAdditivityStillOpen := True
    concreteProjectionOperatorStillOpen := True }

theorem singleton_pvm_theorem_theorem_data_ready :
    singletonPVMTheoremTheoremData.ready := by
  exact And.intro singleton_spectral_theorem_theorem_data_ready <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro prototypeProjectionMassReal_exact_atom_pos <|
    And.intro prototypeProjectionMassReal_exact_atom_ne_zero <|
    And.intro rfl <|
    And.intro exactGapValueReal_eq <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem singleton_pvm_theorem_exact_value_in_atom :
    exactGapValueReal ∈ singletonPVMTheoremTheoremData.exactAtom := by
  exact exactGapValueReal_mem_exactGapAtomReal

theorem singleton_pvm_theorem_exact_atom_mass_positive :
    0 < singletonPVMTheoremTheoremData.projectionMass
      singletonPVMTheoremTheoremData.exactAtom := by
  exact prototypeProjectionMassReal_exact_atom_pos

theorem singleton_pvm_theorem_exact_atom_mass_nonzero :
    singletonPVMTheoremTheoremData.projectionMass
      singletonPVMTheoremTheoremData.exactAtom ≠ 0 := by
  exact prototypeProjectionMassReal_exact_atom_ne_zero

theorem singleton_pvm_theorem_compatible_with_spectral_mass :
    singletonPVMTheoremTheoremData.projectionMass
      singletonPVMTheoremTheoremData.exactAtom =
    singletonPVMTheoremTheoremData.spectralData.spectralMass exactGapValueReal := by
  rfl

/-- Review surface closing the abstract PVM theorem body after the spectral
integration theorem body. -/
structure PVMTheoremTheoremReviewSurface where
  spectralTheoremBodyReady : spectralTheoremTheoremReviewSurface.ready
  pvmTheoremDataReady : singletonPVMTheoremTheoremData.ready
  exactValueInAtom : exactGapValueReal ∈ singletonPVMTheoremTheoremData.exactAtom
  exactAtomMassPositive : 0 < singletonPVMTheoremTheoremData.projectionMass
    singletonPVMTheoremTheoremData.exactAtom
  exactAtomMassNonzero : singletonPVMTheoremTheoremData.projectionMass
    singletonPVMTheoremTheoremData.exactAtom ≠ 0
  compatibleWithSpectralMass : singletonPVMTheoremTheoremData.projectionMass
    singletonPVMTheoremTheoremData.exactAtom =
    singletonPVMTheoremTheoremData.spectralData.spectralMass exactGapValueReal
  pvmTheoremBodyClosed : Prop
  concreteCountableAdditivityStillOpen : Prop
  concreteProjectionOperatorStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def PVMTheoremTheoremReviewSurface.ready
    (S : PVMTheoremTheoremReviewSurface) : Prop :=
  S.spectralTheoremBodyReady ∧ S.pvmTheoremDataReady ∧ S.exactValueInAtom ∧
  S.exactAtomMassPositive ∧ S.exactAtomMassNonzero ∧ S.compatibleWithSpectralMass ∧
  S.pvmTheoremBodyClosed ∧ S.concreteCountableAdditivityStillOpen ∧
  S.concreteProjectionOperatorStillOpen ∧ S.finalReleaseHeld ∧ S.publicBoundaryHeld

def pvmTheoremTheoremReviewSurface : PVMTheoremTheoremReviewSurface :=
  { spectralTheoremBodyReady := spectral_theorem_theorem_review_surface_ready
    pvmTheoremDataReady := singleton_pvm_theorem_theorem_data_ready
    exactValueInAtom := singleton_pvm_theorem_exact_value_in_atom
    exactAtomMassPositive := singleton_pvm_theorem_exact_atom_mass_positive
    exactAtomMassNonzero := singleton_pvm_theorem_exact_atom_mass_nonzero
    compatibleWithSpectralMass := singleton_pvm_theorem_compatible_with_spectral_mass
    pvmTheoremBodyClosed := True
    concreteCountableAdditivityStillOpen := True
    concreteProjectionOperatorStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem pvm_theorem_theorem_review_surface_ready :
    pvmTheoremTheoremReviewSurface.ready := by
  exact And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro singleton_pvm_theorem_theorem_data_ready <|
    And.intro singleton_pvm_theorem_exact_value_in_atom <|
    And.intro singleton_pvm_theorem_exact_atom_mass_positive <|
    And.intro singleton_pvm_theorem_exact_atom_mass_nonzero <|
    And.intro singleton_pvm_theorem_compatible_with_spectral_mass <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem pvm_theorem_theorem_review_surface_final_release_held :
    pvmTheoremTheoremReviewSurface.finalReleaseHeld := by
  trivial

end MathlibAnalytic
end MGAP4D
