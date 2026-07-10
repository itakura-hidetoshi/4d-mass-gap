import MGAP4D.MathlibAnalytic.ExactGapReal
import MGAP4D.MathlibAnalytic.WightmanOSHamiltonianGapSpectrumTheorems

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
A reduced exact-gap spectral core for four-dimensional Yang--Mills models.

The original axiomatic model stores positive energy, vacuum isolation, the first
excitation, its infimum identity, the displayed mass-gap value, and its equality
to the first excitation as separate fields.  For an attained exact Hamiltonian
mass gap these data are consequences rather than independent inputs.

This file packages the smaller input surface and constructs the existing full
axiomatic model from it using the general Mathlib-facing Hamiltonian gap
theorems.
-/

/-- Reduced reconstructed Yang--Mills data in which one attained exact
Hamiltonian mass-gap theorem generates the derived spectral fields of the full
axiomatic model. -/
structure FourDimensionalYangMillsExactGapSpectralCore where
  osWightman : OSWightmanYangMillsAxioms
  spacetimeDim : ℕ
  spacetimeDim_eq_four : spacetimeDim = 4
  H : Type
  [instNormedAddCommGroup : NormedAddCommGroup H]
  [instInnerProductSpace : InnerProductSpace ℝ H]
  [instCompleteSpace : CompleteSpace H]
  vacuum : H
  hamiltonian : H → H
  spectralPVM : Set ℝ → Set H
  energySpectrum : Set ℝ
  energyMomentumSpectrum : Set (ℝ × (Fin 3 → ℝ))
  hamiltonianSelfAdjoint : Prop
  exactHamiltonianMassGap :
    HasHamiltonianMassGap energySpectrum exactGapValueReal
  exactGapAttained : exactGapValueReal ∈ energySpectrum

/-- The reduced core derives positivity of the whole Hamiltonian spectrum. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.positiveEnergy
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    ∀ E ∈ C.energySpectrum, 0 ≤ E := by
  exact hasHamiltonianMassGap_positive_energy C.exactHamiltonianMassGap

/-- The reduced core derives isolation of the vacuum using the exact gap itself
as an isolating radius. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.vacuumIsolated
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    ∃ δ : ℝ,
      0 < δ ∧ Set.Ioo 0 δ ∩ C.energySpectrum = ∅ := by
  exact ⟨
    exactGapValueReal,
    C.exactHamiltonianMassGap.1,
    hasHamiltonianMassGap_vacuum_isolated C.exactHamiltonianMassGap⟩

/-- The attained exact gap is the least non-vacuum spectral energy. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.exactGapIsLeast
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    IsLeast
      (C.energySpectrum \ ({0} : Set ℝ))
      exactGapValueReal := by
  exact hasHamiltonianMassGap_isLeast_nonvacuum
    C.exactHamiltonianMassGap C.exactGapAttained

/-- The non-vacuum spectral infimum is the attained exact gap. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.sInfNonvacuumEqExactGap
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    sInf (C.energySpectrum \ ({0} : Set ℝ)) = exactGapValueReal := by
  exact hasHamiltonianMassGap_sInf_nonvacuum_eq
    C.exactHamiltonianMassGap C.exactGapAttained

/-- Construct the existing full axiomatic Yang--Mills model from the reduced
exact-gap spectral core.

The fields `positiveEnergy`, `vacuumIsolated`, `firstExcitation`, and
`massGapValue` are generated rather than supplied independently. -/
def FourDimensionalYangMillsExactGapSpectralCore.toAxiomaticModel
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    FourDimensionalYangMillsAxiomaticModel where
  osWightman := C.osWightman
  spacetimeDim := C.spacetimeDim
  spacetimeDim_eq_four := C.spacetimeDim_eq_four
  H := C.H
  instNormedAddCommGroup := C.instNormedAddCommGroup
  instInnerProductSpace := C.instInnerProductSpace
  instCompleteSpace := C.instCompleteSpace
  vacuum := C.vacuum
  hamiltonian := C.hamiltonian
  spectralPVM := C.spectralPVM
  energySpectrum := C.energySpectrum
  energyMomentumSpectrum := C.energyMomentumSpectrum
  hamiltonianSelfAdjoint := C.hamiltonianSelfAdjoint
  vacuumEnergyZero := C.exactHamiltonianMassGap.2.1
  positiveEnergy := C.positiveEnergy
  vacuumIsolated := C.vacuumIsolated
  firstExcitation := exactGapValueReal
  firstExcitation_mem := C.exactGapAttained
  firstExcitation_pos := C.exactHamiltonianMassGap.1
  firstExcitation_is_sInf_nonvacuum := C.sInfNonvacuumEqExactGap.symm
  massGapValue := exactGapValueReal
  massGapValue_eq_firstExcitation := rfl

/-- The generated full model preserves the reduced core energy spectrum. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.toAxiomaticModel_energySpectrum
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    C.toAxiomaticModel.energySpectrum = C.energySpectrum := by
  rfl

/-- The generated full model defines its first excitation to be the exact gap. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.toAxiomaticModel_firstExcitation
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    C.toAxiomaticModel.firstExcitation = exactGapValueReal := by
  rfl

/-- The generated full model defines its displayed mass-gap value to be the exact
gap. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.toAxiomaticModel_massGapValue
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    C.toAxiomaticModel.massGapValue = exactGapValueReal := by
  rfl

/-- The generated full model has the model-level mass-gap predicate without an
additional witness field. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.toAxiomaticModel_hasMassGap
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    C.toAxiomaticModel.hasMassGap := by
  exact ⟨
    exactGapValueReal,
    C.exactHamiltonianMassGap.1,
    C.exactGapAttained,
    C.sInfNonvacuumEqExactGap.symm⟩

/-- The generated model's nonzero spectrum has the exact gap as its least
member. -/
theorem FourDimensionalYangMillsExactGapSpectralCore.toAxiomaticModel_exactGapIsLeast
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    IsLeast
      (C.toAxiomaticModel.energySpectrum \ ({0} : Set ℝ))
      exactGapValueReal := by
  exact C.exactGapIsLeast

/-- Certificate recording the derived full-model fields from the smaller exact
spectral input. -/
structure FourDimensionalYangMillsExactGapSpectralCoreCertificate
    (C : FourDimensionalYangMillsExactGapSpectralCore) where
  positiveEnergy : ∀ E ∈ C.energySpectrum, 0 ≤ E
  vacuumIsolated :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo 0 δ ∩ C.energySpectrum = ∅
  exactGapLeast :
    IsLeast (C.energySpectrum \ ({0} : Set ℝ)) exactGapValueReal
  exactGapInfimum :
    sInf (C.energySpectrum \ ({0} : Set ℝ)) = exactGapValueReal
  generatedMassGap : C.toAxiomaticModel.hasMassGap
  generatedFirstExcitation :
    C.toAxiomaticModel.firstExcitation = exactGapValueReal
  generatedMassGapValue :
    C.toAxiomaticModel.massGapValue = exactGapValueReal

/-- Canonical certificate for the reduced exact-gap spectral core. -/
def fourDimensionalYangMillsExactGapSpectralCoreCertificate
    (C : FourDimensionalYangMillsExactGapSpectralCore) :
    FourDimensionalYangMillsExactGapSpectralCoreCertificate C where
  positiveEnergy := C.positiveEnergy
  vacuumIsolated := C.vacuumIsolated
  exactGapLeast := C.exactGapIsLeast
  exactGapInfimum := C.sInfNonvacuumEqExactGap
  generatedMassGap := C.toAxiomaticModel_hasMassGap
  generatedFirstExcitation := C.toAxiomaticModel_firstExcitation
  generatedMassGapValue := C.toAxiomaticModel_massGapValue

end

end MathlibAnalytic
end MGAP4D
