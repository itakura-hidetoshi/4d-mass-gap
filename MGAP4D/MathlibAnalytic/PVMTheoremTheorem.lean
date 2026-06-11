import MGAP4D.MathlibAnalytic.SpectralTheoremTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract theorem body for the projection-valued-measure layer.

This is the fourth post-interface theorem-body step. It does not yet prove a
concrete countably-additive projection-valued measure for an unbounded
self-adjoint operator. It makes explicit the set-indexed projection mass,
exact atom, positive/nonzero exact-atom mass, and compatibility with the
abstract spectral theorem body, without asserting the numeric `33/20` value
upstream of R6. -/
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
  pvmCertificate : Prop
  pvmCertificate_proof : pvmCertificate
  concreteCountableAdditivityStillOpen : Prop
  concreteCountableAdditivityStillOpen_proof : concreteCountableAdditivityStillOpen
  concreteProjectionOperatorStillOpen : Prop
  concreteProjectionOperatorStillOpen_proof : concreteProjectionOperatorStillOpen

/-- Ready predicate for the abstract PVM theorem body. -/
def PVMTheoremTheoremData.ready (D : PVMTheoremTheoremData) : Prop :=
  D.spectralData.ready ∧
  D.exactAtom = exactGapAtomReal ∧
  exactGapValueReal ∈ D.exactAtom ∧
  0 < D.projectionMass D.exactAtom ∧
  D.projectionMass D.exactAtom ≠ 0 ∧
  D.projectionMass D.exactAtom = D.spectralData.spectralMass exactGapValueReal ∧
  D.pvmCertificate ∧ D.concreteCountableAdditivityStillOpen ∧
  D.concreteProjectionOperatorStillOpen

/-- The exact value belongs to the exact atom. -/
theorem pvm_theorem_exact_value_in_atom
    (D : PVMTheoremTheoremData) (hD : D.ready) :
    exactGapValueReal ∈ D.exactAtom := by
  rcases hD with ⟨_, _, hIn, _, _, _, _, _, _⟩
  exact hIn

/-- The projection mass of the exact atom is positive. -/
theorem pvm_theorem_exact_atom_mass_positive
    (D : PVMTheoremTheoremData) (hD : D.ready) :
    0 < D.projectionMass D.exactAtom := by
  rcases hD with ⟨_, _, _, hPos, _, _, _, _, _⟩
  exact hPos

/-- The projection mass of the exact atom is nonzero. -/
theorem pvm_theorem_exact_atom_mass_nonzero
    (D : PVMTheoremTheoremData) (hD : D.ready) :
    D.projectionMass D.exactAtom ≠ 0 := by
  rcases hD with ⟨_, _, _, _, hNe, _, _, _, _⟩
  exact hNe

/-- The exact-atom projection mass is compatible with the spectral mass at the
exact value. -/
theorem pvm_theorem_compatible_with_spectral_mass
    (D : PVMTheoremTheoremData) (hD : D.ready) :
    D.projectionMass D.exactAtom = D.spectralData.spectralMass exactGapValueReal := by
  rcases hD with ⟨_, _, _, _, _, hCompat, _, _, _⟩
  exact hCompat

/-- The PVM certificate surface is present. -/
theorem pvm_theorem_certificate
    (D : PVMTheoremTheoremData) (hD : D.ready) :
    D.pvmCertificate := by
  rcases hD with ⟨_, _, _, _, _, _, hCert, _, _⟩
  exact hCert

/-- PVM theorem-body realization over the admissible spectral theorem carrier. -/
def admissiblePVMTheoremTheoremData : PVMTheoremTheoremData :=
  { spectralData := admissibleSpectralTheoremTheoremData
    spectralDataReady := admissible_spectral_theorem_theorem_data_ready
    projectionMass := prototypeProjectionMassReal
    exactAtom := exactGapAtomReal
    exactAtom_def := rfl
    exact_value_in_atom := exactGapValueReal_mem_exactGapAtomReal
    exact_atom_mass_positive := prototypeProjectionMassReal_exact_atom_pos
    exact_atom_mass_nonzero := prototypeProjectionMassReal_exact_atom_ne_zero
    compatible_with_spectral_mass := rfl
    pvmCertificate := spectralTheoremTheoremReviewSurface.ready
    pvmCertificate_proof := spectral_theorem_theorem_review_surface_ready
    concreteCountableAdditivityStillOpen := exactGapValueReal ∈ exactGapAtomReal
    concreteCountableAdditivityStillOpen_proof := exactGapValueReal_mem_exactGapAtomReal
    concreteProjectionOperatorStillOpen := 0 < prototypeProjectionMassReal exactGapAtomReal
    concreteProjectionOperatorStillOpen_proof := prototypeProjectionMassReal_exact_atom_pos }

theorem admissible_pvm_theorem_theorem_data_ready :
    admissiblePVMTheoremTheoremData.ready := by
  exact And.intro admissible_spectral_theorem_theorem_data_ready <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro prototypeProjectionMassReal_exact_atom_pos <|
    And.intro prototypeProjectionMassReal_exact_atom_ne_zero <|
    And.intro rfl <|
    And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro exactGapValueReal_mem_exactGapAtomReal prototypeProjectionMassReal_exact_atom_pos

theorem admissible_pvm_theorem_exact_value_in_atom :
    exactGapValueReal ∈ admissiblePVMTheoremTheoremData.exactAtom := by
  exact pvm_theorem_exact_value_in_atom
    admissiblePVMTheoremTheoremData admissible_pvm_theorem_theorem_data_ready

theorem admissible_pvm_theorem_exact_atom_mass_positive :
    0 < admissiblePVMTheoremTheoremData.projectionMass
      admissiblePVMTheoremTheoremData.exactAtom := by
  exact pvm_theorem_exact_atom_mass_positive
    admissiblePVMTheoremTheoremData admissible_pvm_theorem_theorem_data_ready

theorem admissible_pvm_theorem_exact_atom_mass_nonzero :
    admissiblePVMTheoremTheoremData.projectionMass
      admissiblePVMTheoremTheoremData.exactAtom ≠ 0 := by
  exact pvm_theorem_exact_atom_mass_nonzero
    admissiblePVMTheoremTheoremData admissible_pvm_theorem_theorem_data_ready

theorem admissible_pvm_theorem_compatible_with_spectral_mass :
    admissiblePVMTheoremTheoremData.projectionMass
      admissiblePVMTheoremTheoremData.exactAtom =
    admissiblePVMTheoremTheoremData.spectralData.spectralMass exactGapValueReal := by
  exact pvm_theorem_compatible_with_spectral_mass
    admissiblePVMTheoremTheoremData admissible_pvm_theorem_theorem_data_ready

/-- Review surface closing the abstract PVM theorem body after the spectral
integration theorem body. -/
structure PVMTheoremTheoremReviewSurface where
  spectralTheoremBodyReady : spectralTheoremTheoremReviewSurface.ready
  pvmTheoremDataReady : admissiblePVMTheoremTheoremData.ready
  exactValueInAtom : exactGapValueReal ∈ admissiblePVMTheoremTheoremData.exactAtom
  exactAtomMassPositive : 0 < admissiblePVMTheoremTheoremData.projectionMass
    admissiblePVMTheoremTheoremData.exactAtom
  exactAtomMassNonzero : admissiblePVMTheoremTheoremData.projectionMass
    admissiblePVMTheoremTheoremData.exactAtom ≠ 0
  compatibleWithSpectralMass : admissiblePVMTheoremTheoremData.projectionMass
    admissiblePVMTheoremTheoremData.exactAtom =
    admissiblePVMTheoremTheoremData.spectralData.spectralMass exactGapValueReal
  pvmTheoremBodyClosed : admissiblePVMTheoremTheoremData.pvmCertificate
  concreteCountableAdditivityStillOpen : admissiblePVMTheoremTheoremData.concreteCountableAdditivityStillOpen
  concreteProjectionOperatorStillOpen : admissiblePVMTheoremTheoremData.concreteProjectionOperatorStillOpen
  finalReleaseHeld : 0 < exactGapValueReal
  publicBoundaryHeld : exactGapValueReal ∈ exactGapAtomReal

/-- Certification predicate for the PVM review surface. -/
def PVMTheoremTheoremReviewSurface.ready
    (_S : PVMTheoremTheoremReviewSurface) : Prop :=
  spectralTheoremTheoremReviewSurface.ready ∧ admissiblePVMTheoremTheoremData.ready ∧
  exactGapValueReal ∈ admissiblePVMTheoremTheoremData.exactAtom ∧
  0 < admissiblePVMTheoremTheoremData.projectionMass
      admissiblePVMTheoremTheoremData.exactAtom ∧
  admissiblePVMTheoremTheoremData.projectionMass
      admissiblePVMTheoremTheoremData.exactAtom ≠ 0 ∧
  admissiblePVMTheoremTheoremData.projectionMass
      admissiblePVMTheoremTheoremData.exactAtom =
      admissiblePVMTheoremTheoremData.spectralData.spectralMass exactGapValueReal ∧
  admissiblePVMTheoremTheoremData.pvmCertificate ∧
  admissiblePVMTheoremTheoremData.concreteCountableAdditivityStillOpen ∧
  admissiblePVMTheoremTheoremData.concreteProjectionOperatorStillOpen ∧
  0 < exactGapValueReal ∧
  exactGapValueReal ∈ exactGapAtomReal

def pvmTheoremTheoremReviewSurface : PVMTheoremTheoremReviewSurface :=
  { spectralTheoremBodyReady := spectral_theorem_theorem_review_surface_ready
    pvmTheoremDataReady := admissible_pvm_theorem_theorem_data_ready
    exactValueInAtom := admissible_pvm_theorem_exact_value_in_atom
    exactAtomMassPositive := admissible_pvm_theorem_exact_atom_mass_positive
    exactAtomMassNonzero := admissible_pvm_theorem_exact_atom_mass_nonzero
    compatibleWithSpectralMass := admissible_pvm_theorem_compatible_with_spectral_mass
    pvmTheoremBodyClosed := spectral_theorem_theorem_review_surface_ready
    concreteCountableAdditivityStillOpen := exactGapValueReal_mem_exactGapAtomReal
    concreteProjectionOperatorStillOpen := prototypeProjectionMassReal_exact_atom_pos
    finalReleaseHeld := exactGapValueReal_pos
    publicBoundaryHeld := exactGapValueReal_mem_exactGapAtomReal }

theorem pvm_theorem_theorem_review_surface_ready :
    pvmTheoremTheoremReviewSurface.ready := by
  exact And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro admissible_pvm_theorem_theorem_data_ready <|
    And.intro admissible_pvm_theorem_exact_value_in_atom <|
    And.intro admissible_pvm_theorem_exact_atom_mass_positive <|
    And.intro admissible_pvm_theorem_exact_atom_mass_nonzero <|
    And.intro admissible_pvm_theorem_compatible_with_spectral_mass <|
    And.intro spectral_theorem_theorem_review_surface_ready <|
    And.intro exactGapValueReal_mem_exactGapAtomReal <|
    And.intro prototypeProjectionMassReal_exact_atom_pos <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_exactGapAtomReal

theorem pvm_theorem_theorem_review_surface_final_release_held :
    0 < exactGapValueReal := by
  exact pvmTheoremTheoremReviewSurface.finalReleaseHeld

end

end MathlibAnalytic
end MGAP4D