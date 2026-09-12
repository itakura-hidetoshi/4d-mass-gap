import MGAP4D.MathlibAnalytic.WightmanOSPVMVacuumOrthogonality
import MGAP4D.MathlibAnalytic.WightmanOSScalarSpectralMeasurePositivity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Positive singleton mass in a scalar spectral measure forces the corresponding
singleton PVM projection vector to be nonzero. -/
theorem scalar_spectral_measure_projection_ne_zero_of_singleton_mass_pos
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (psi : M.H) (E : ℝ)
    (hMass : 0 < (R.scalarMeasure psi).real ({E} : Set ℝ)) :
    M.spectralPVM.projection ({E} : Set ℝ) psi ≠ 0 := by
  rw [R.singletonMass_eq_squaredProjectionNorm psi E] at hMass
  intro hProjection
  rw [hProjection, norm_zero] at hMass
  norm_num at hMass

/-- Construct the concrete nonzero spectral-PVM witness from a positive atom of
one scalar spectral measure. -/
def explicitWightmanOSNonzeroSpectralPVMWitnessOfPositiveSingletonMass
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    {E : ℝ}
    (hEnergy : E ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : E ≠ 0)
    (psi : M.H)
    (hMass : 0 < (R.scalarMeasure psi).real ({E} : Set ℝ)) :
    ExplicitWightmanOSNonzeroSpectralPVMWitness M :=
  { energy := E
    energy_mem := hEnergy
    energy_ne_zero := hEnergyZero
    source := psi
    projected_ne_zero :=
      scalar_spectral_measure_projection_ne_zero_of_singleton_mass_pos
        R psi E hMass }

/-- The standard PVM composition law and a positive scalar singleton mass build
the vacuum-orthogonal spectrum bridge without a separately supplied PVM vector. -/
def explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPositiveSingletonMass
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    {E : ℝ}
    (hEnergy : E ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : E ≠ 0)
    (psi : M.H)
    (hMass : 0 < (R.scalarMeasure psi).real ({E} : Set ℝ)) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVMComposition
    M hComposition
    (explicitWightmanOSNonzeroSpectralPVMWitnessOfPositiveSingletonMass
      M R hEnergy hEnergyZero psi hMass)

/-- A positive scalar singleton mass supplies the nontriviality input in the
physical vacuum-orthogonal spectral-gap theorem. -/
theorem explicit_wightman_os_positive_singleton_mass_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    {E m : ℝ}
    (hEnergy : E ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : E ≠ 0)
    (psi : M.H)
    (hMass : 0 < (R.scalarMeasure psi).real ({E} : Set ℝ))
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    0 < m ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆ Set.Ici m ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = m := by
  exact explicit_wightman_os_pvm_composition_vacuum_orthogonal_spectrum_gap
    M hComposition
    (explicitWightmanOSNonzeroSpectralPVMWitnessOfPositiveSingletonMass
      M R hEnergy hEnergyZero psi hMass)
    hRelGap hmSpectrum

/-- Exact-gap specialization whose excitation witness is obtained from positive
singleton scalar spectral mass. -/
theorem explicit_wightman_os_positive_singleton_mass_vacuum_orthogonal_exact_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    {E : ℝ}
    (hEnergy : E ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : E ≠ 0)
    (psi : M.H)
    (hMass : 0 < (R.scalarMeasure psi).real ({E} : Set ℝ))
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum : exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact explicit_wightman_os_positive_singleton_mass_vacuum_orthogonal_spectrum_gap
    M R hComposition hEnergy hEnergyZero psi hMass hRelGap hExactSpectrum

/-- Full physical gap certificate with nontriviality derived from positive
singleton scalar spectral mass. -/
def explicitWightmanOSPositiveSingletonMassVacuumOrthogonalGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    {E m : ℝ}
    (hEnergy : E ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : E ≠ 0)
    (psi : M.H)
    (hMass : 0 < (R.scalarMeasure psi).real ({E} : Set ℝ))
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSVacuumOrthogonalGapCertificate M
      (explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPositiveSingletonMass
        M R hComposition hEnergy hEnergyZero psi hMass) m :=
  explicitWightmanOSVacuumOrthogonalGapCertificate
    M
    (explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPositiveSingletonMass
      M R hComposition hEnergy hEnergyZero psi hMass)
    hRelGap hmSpectrum

end

end MathlibAnalytic
end MGAP4D
