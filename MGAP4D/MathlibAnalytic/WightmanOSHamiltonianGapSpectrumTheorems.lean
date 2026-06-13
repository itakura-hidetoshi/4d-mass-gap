import MGAP4D.MathlibAnalytic.WightmanOSExplicitEnergyMomentumMassGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A Hamiltonian mass gap places the whole energy spectrum in the union of the
vacuum point and the closed half-line above the gap. -/
theorem hasHamiltonianMassGap_spectrum_subset
    {energySpectrum : Set ℝ} {m : ℝ}
    (hGap : HasHamiltonianMassGap energySpectrum m) :
    energySpectrum ⊆ ({0} : Set ℝ) ∪ Set.Ici m := by
  intro E hE
  by_cases hE0 : E = 0
  · left
    simpa [hE0]
  · right
    exact hGap.2.2 E hE hE0

/-- A Hamiltonian mass gap isolates the vacuum: no spectral value lies strictly
between zero and the gap. -/
theorem hasHamiltonianMassGap_vacuum_isolated
    {energySpectrum : Set ℝ} {m : ℝ}
    (hGap : HasHamiltonianMassGap energySpectrum m) :
    Set.Ioo 0 m ∩ energySpectrum = ∅ := by
  ext E
  constructor
  · intro hE
    rcases hE with ⟨hInterval, hSpectrum⟩
    have hE0 : E ≠ 0 := ne_of_gt hInterval.1
    have hmE : m ≤ E := hGap.2.2 E hSpectrum hE0
    exact (not_lt_of_ge hmE hInterval.2).elim
  · intro hE
    simpa using hE

/-- The mass-gap predicate itself implies the positive-energy condition for the
Hamiltonian spectrum. -/
theorem hasHamiltonianMassGap_positive_energy
    {energySpectrum : Set ℝ} {m : ℝ}
    (hGap : HasHamiltonianMassGap energySpectrum m) :
    ∀ E ∈ energySpectrum, 0 ≤ E := by
  intro E hE
  by_cases hE0 : E = 0
  · simpa [hE0]
  · have hmE : m ≤ E := hGap.2.2 E hE hE0
    exact le_trans (le_of_lt hGap.1) hmE

/-- Conversely, positive energy together with a spectral interval free of
excitations produces the Hamiltonian mass-gap predicate. -/
theorem positive_energy_and_vacuum_isolation_imply_mass_gap
    {energySpectrum : Set ℝ} {m : ℝ}
    (hm : 0 < m)
    (hVacuum : 0 ∈ energySpectrum)
    (hPositive : ∀ E ∈ energySpectrum, 0 ≤ E)
    (hIsolated : Set.Ioo 0 m ∩ energySpectrum = ∅) :
    HasHamiltonianMassGap energySpectrum m := by
  refine ⟨hm, hVacuum, ?_⟩
  intro E hE hE0
  by_contra hNot
  have hEm : E < m := lt_of_not_ge hNot
  have hEpos : 0 < E := lt_of_le_of_ne (hPositive E hE) (Ne.symm hE0)
  have hForbidden : E ∈ Set.Ioo 0 m ∩ energySpectrum :=
    ⟨⟨hEpos, hEm⟩, hE⟩
  rw [hIsolated] at hForbidden
  exact hForbidden

/-- If the lower edge is actually attained, then it is the least point of the
non-vacuum Hamiltonian spectrum. -/
theorem hasHamiltonianMassGap_isLeast_nonvacuum
    {energySpectrum : Set ℝ} {m : ℝ}
    (hGap : HasHamiltonianMassGap energySpectrum m)
    (hmSpectrum : m ∈ energySpectrum) :
    IsLeast (energySpectrum \ ({0} : Set ℝ)) m := by
  refine ⟨?_, ?_⟩
  · exact ⟨hmSpectrum, by simp [ne_of_gt hGap.1]⟩
  · intro E hE
    have hE0 : E ≠ 0 := by
      simpa using hE.2
    exact hGap.2.2 E hE.1 hE0

/-- If the gap is attained, the infimum of the non-vacuum spectrum is exactly the
mass-gap value. -/
theorem hasHamiltonianMassGap_sInf_nonvacuum_eq
    {energySpectrum : Set ℝ} {m : ℝ}
    (hGap : HasHamiltonianMassGap energySpectrum m)
    (hmSpectrum : m ∈ energySpectrum) :
    sInf (energySpectrum \ ({0} : Set ℝ)) = m := by
  have hLeast : IsLeast (energySpectrum \ ({0} : Set ℝ)) m :=
    hasHamiltonianMassGap_isLeast_nonvacuum hGap hmSpectrum
  have hBdd : BddBelow (energySpectrum \ ({0} : Set ℝ)) :=
    ⟨m, hLeast.2⟩
  have hNonempty : (energySpectrum \ ({0} : Set ℝ)).Nonempty :=
    ⟨m, hLeast.1⟩
  apply le_antisymm
  · exact csInf_le hBdd hLeast.1
  · exact le_csInf hNonempty hLeast.2

/-- The explicit reconstructed Wightman/OS model has an isolated vacuum whenever
its joint energy-momentum spectrum has a relativistic mass gap. -/
theorem explicit_wightman_os_vacuum_isolated
    (M : ExplicitWightmanOSReconstructedModel) {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m) :
    Set.Ioo 0 m ∩ M.hamiltonianEnergySpectrum = ∅ := by
  apply hasHamiltonianMassGap_vacuum_isolated
  exact explicit_wightman_os_reconstruction_has_mass_gap M hRelGap

/-- If the relativistic lower edge is also realized as a Hamiltonian spectral
point, it is the exact non-vacuum spectral threshold. -/
theorem explicit_wightman_os_mass_gap_sInf_nonvacuum_eq
    (M : ExplicitWightmanOSReconstructedModel) {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = m := by
  exact hasHamiltonianMassGap_sInf_nonvacuum_eq
    (explicit_wightman_os_reconstruction_has_mass_gap M hRelGap)
    hmSpectrum

/-- Full spectral lower-edge certificate for the explicit Wightman/OS model. -/
structure ExplicitWightmanOSSpectralLowerEdgeCertificate
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ) where
  relativisticGap : HasRelativisticMassGap M.energyMomentumSpectrum m
  hamiltonianGap : M.HasMassGap m
  spectrumSubset :
    M.hamiltonianEnergySpectrum ⊆ ({0} : Set ℝ) ∪ Set.Ici m
  positiveEnergy :
    ∀ E ∈ M.hamiltonianEnergySpectrum, 0 ≤ E
  vacuumIsolated :
    Set.Ioo 0 m ∩ M.hamiltonianEnergySpectrum = ∅

/-- Construct the spectral lower-edge certificate from the relativistic joint
spectrum condition. -/
def explicitWightmanOSSpectralLowerEdgeCertificate
    (M : ExplicitWightmanOSReconstructedModel) {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m) :
    ExplicitWightmanOSSpectralLowerEdgeCertificate M m := by
  have hHam : M.HasMassGap m :=
    explicit_wightman_os_reconstruction_has_mass_gap M hRelGap
  exact
    { relativisticGap := hRelGap
      hamiltonianGap := hHam
      spectrumSubset := hasHamiltonianMassGap_spectrum_subset hHam
      positiveEnergy := hasHamiltonianMassGap_positive_energy hHam
      vacuumIsolated := hasHamiltonianMassGap_vacuum_isolated hHam }

end

end MathlibAnalytic
end MGAP4D
