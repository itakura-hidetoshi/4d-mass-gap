import MGAP4D.MathlibAnalytic.ExplicitWightmanOSExactGapSpectralSupportCore
import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMSpectralSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Connect the explicit exact-gap spectral core directly to the open-neighborhood
support of the actual bounded PVM on the vacuum-orthogonal Hilbert sector.

Unlike singleton spectral detection, this support records continuous spectrum:
an energy belongs when every open neighborhood has a nonzero PVM projection on
some physical vacuum-orthogonal vector.
-/

/-- The pure PVM open support is the non-vacuum energy spectrum of the exact-gap
core generated from the same explicit Wightman model. -/
theorem ExplicitWightmanOSCanonicalPVMOpenSupportBridge.pvmOpenSupport_eq_exactGapCore_nonvacuum
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    M.vacuumOrthogonalPVMOpenSupport =
      (M.toExactGapSpectralCore hGap hExactSpectrum).energySpectrum \
        ({0} : Set ℝ) := by
  rw [B.pvmOpenSupport_eq_restrictedSpectrum]
  exact B.restrictedSpectrum_eq_nonvacuum

/-- Vacuum energy is absent from the pure PVM support on the physical excitation
sector. -/
theorem ExplicitWightmanOSCanonicalPVMOpenSupportBridge.zero_not_mem_pvmOpenSupport
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M) :
    0 ∉ M.vacuumOrthogonalPVMOpenSupport := by
  rw [B.pvmOpenSupport_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_zero_not_mem
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge

/-- Any Hamiltonian mass gap bounds the complete PVM open support from below. -/
theorem ExplicitWightmanOSCanonicalPVMOpenSupportBridge.pvmOpenSupport_subset_Ici
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    {m : ℝ}
    (hGap : HasHamiltonianMassGap M.hamiltonianEnergySpectrum m) :
    M.vacuumOrthogonalPVMOpenSupport ⊆ Set.Ici m := by
  rw [B.pvmOpenSupport_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_subset_Ici
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
    hGap

/-- Threshold attainment puts the exact gap in the pure PVM support, without
requiring a singleton spectral projection. -/
theorem ExplicitWightmanOSCanonicalPVMOpenSupportBridge.exactGap_mem_pvmOpenSupport
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    exactGapValueReal ∈ M.vacuumOrthogonalPVMOpenSupport := by
  rw [B.pvmOpenSupport_eq_exactGapCore_nonvacuum hGap hExactSpectrum]
  exact ⟨hExactSpectrum, by simpa using (ne_of_gt hGap.1)⟩

/-- The exact gap is the least energy in the full PVM open support. -/
theorem ExplicitWightmanOSCanonicalPVMOpenSupportBridge.exactGap_isLeast_pvmOpenSupport
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    IsLeast M.vacuumOrthogonalPVMOpenSupport exactGapValueReal := by
  refine ⟨B.exactGap_mem_pvmOpenSupport hGap hExactSpectrum, ?_⟩
  intro energy hEnergy
  exact (B.pvmOpenSupport_subset_Ici hGap) hEnergy

/-- The infimum of the complete PVM open support is the attained exact gap. -/
theorem ExplicitWightmanOSCanonicalPVMOpenSupportBridge.pvmOpenSupport_sInf_eq_exactGap
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    sInf M.vacuumOrthogonalPVMOpenSupport = exactGapValueReal := by
  rw [B.pvmOpenSupport_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_sInf_eq
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
    hGap hExactSpectrum

/-- Compact physical statement joining the actual canonical restricted
Hamiltonian, its pure PVM support, and the exact-gap core. -/
abbrev ExplicitWightmanOSExactGapPVMOpenSupportProp
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) : Prop :=
  let core := M.toExactGapSpectralCore hGap hExactSpectrum
  IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian ∧
    Dense ((M.canonicalVacuumOrthogonalHamiltonian.domain :
      Set M.VacuumOrthogonalHilbert)) ∧
    LinearPMap.IsClosed M.canonicalVacuumOrthogonalHamiltonian ∧
    M.vacuumOrthogonalPVMOpenSupport =
      core.energySpectrum \ ({0} : Set ℝ) ∧
    0 ∉ M.vacuumOrthogonalPVMOpenSupport ∧
    IsLeast M.vacuumOrthogonalPVMOpenSupport exactGapValueReal ∧
    sInf M.vacuumOrthogonalPVMOpenSupport = exactGapValueReal

/-- The canonical restricted Hamiltonian and its continuous-spectrum-compatible
PVM support satisfy the exact-gap theorem simultaneously. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSExactGapPVMOpenSupportProp
      M B hGap hExactSpectrum := by
  exact ⟨
    B.canonicalRestrictedSelfAdjoint,
    canonical_vacuum_orthogonal_hamiltonian_dense_domain
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge,
    canonical_vacuum_orthogonal_hamiltonian_isClosed
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge,
    B.pvmOpenSupport_eq_exactGapCore_nonvacuum hGap hExactSpectrum,
    B.zero_not_mem_pvmOpenSupport,
    B.exactGap_isLeast_pvmOpenSupport hGap hExactSpectrum,
    B.pvmOpenSupport_sInf_eq_exactGap hGap hExactSpectrum⟩

end

end MathlibAnalytic
end MGAP4D
