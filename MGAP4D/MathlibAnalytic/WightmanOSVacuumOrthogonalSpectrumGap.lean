import MGAP4D.MathlibAnalytic.WightmanOSHamiltonianGapSpectrumTheorems
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The one-dimensional vacuum line in the reconstructed physical Hilbert space. -/
def ExplicitWightmanOSReconstructedModel.vacuumLine
    (M : ExplicitWightmanOSReconstructedModel) : Submodule ℝ M.H :=
  ℝ ∙ M.vacuum

/-- The physical non-vacuum Hilbert sector `Ω⊥`, defined as the orthogonal
complement of the vacuum line. -/
def ExplicitWightmanOSReconstructedModel.vacuumOrthogonal
    (M : ExplicitWightmanOSReconstructedModel) : Submodule ℝ M.H :=
  (M.vacuumLine)ᗮ

/-- Carrier notation for the complete Hilbert subspace `Ω⊥`.  Mathlib supplies
the inherited normed additive group and inner-product-space structures, and the
orthogonal-complement construction supplies completeness. -/
abbrev ExplicitWightmanOSReconstructedModel.VacuumOrthogonalHilbert
    (M : ExplicitWightmanOSReconstructedModel) : Type :=
  M.vacuumOrthogonal

/-- Membership in `Ω⊥` is exactly orthogonality to the reconstructed vacuum. -/
theorem explicit_wightman_os_mem_vacuumOrthogonal_iff
    (M : ExplicitWightmanOSReconstructedModel) (ψ : M.H) :
    ψ ∈ M.vacuumOrthogonal ↔ inner ℝ M.vacuum ψ = 0 := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonal,
    ExplicitWightmanOSReconstructedModel.vacuumLine] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := M.vacuum) (v := ψ))

/-- The normalized vacuum does not itself belong to `Ω⊥`. -/
theorem explicit_wightman_os_vacuum_not_mem_vacuumOrthogonal
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuum ∉ M.vacuumOrthogonal := by
  intro hVacuumOrthogonal
  have hInner : inner ℝ M.vacuum M.vacuum = 0 :=
    (explicit_wightman_os_mem_vacuumOrthogonal_iff M M.vacuum).mp
      hVacuumOrthogonal
  have hVacuumZero : M.vacuum = 0 :=
    inner_self_eq_zero.mp hInner
  have hImpossible : (0 : ℝ) = 1 := by
    simpa [hVacuumZero] using M.vacuum_norm
  norm_num at hImpossible

/-- The additional spectral identification needed to interpret the nonzero
Hamiltonian spectrum as the spectrum carried by `Ω⊥`.

The equality of spectra and the PVM range statement are kept explicit.  They are
not derivable from the repository's current finite-additivity-only PVM interface
without adding the usual projection multiplication law. -/
structure ExplicitWightmanOSVacuumOrthogonalSpectrumBridge
    (M : ExplicitWightmanOSReconstructedModel) where
  restrictedSpectrum : Set ℝ
  restrictedSpectrum_eq_nonvacuum :
    restrictedSpectrum = M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)
  pvm_nonvacuum_range_orthogonal :
    ∀ {E : ℝ}, E ∈ restrictedSpectrum → ∀ ψ : M.H,
      M.spectralPVM.projection ({E} : Set ℝ) ψ ∈ M.vacuumOrthogonal
  orthogonalSector_nontrivial :
    ∃ ψ : M.VacuumOrthogonalHilbert, (ψ : M.H) ≠ 0

/-- Zero is absent from the Hamiltonian spectrum restricted to `Ω⊥`. -/
theorem vacuum_orthogonal_restrictedSpectrum_zero_not_mem
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M) :
    0 ∉ B.restrictedSpectrum := by
  rw [B.restrictedSpectrum_eq_nonvacuum]
  simp

/-- Every energy in the `Ω⊥`-restricted spectrum lies above a Hamiltonian mass
gap. -/
theorem vacuum_orthogonal_restrictedSpectrum_lower_bound
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    {m : ℝ} (hGap : M.HasMassGap m) :
    ∀ E ∈ B.restrictedSpectrum, m ≤ E := by
  intro E hE
  rw [B.restrictedSpectrum_eq_nonvacuum] at hE
  exact hGap.2.2 E hE.1 (by simpa using hE.2)

/-- Set-theoretic form of the spectral lower bound on `Ω⊥`. -/
theorem vacuum_orthogonal_restrictedSpectrum_subset_Ici
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    {m : ℝ} (hGap : M.HasMassGap m) :
    B.restrictedSpectrum ⊆ Set.Ici m := by
  intro E hE
  exact vacuum_orthogonal_restrictedSpectrum_lower_bound B hGap E hE

/-- When the lower edge is attained, the infimum of the spectrum on `Ω⊥` is the
mass-gap value. -/
theorem vacuum_orthogonal_restrictedSpectrum_sInf_eq
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    {m : ℝ} (hGap : M.HasMassGap m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    sInf B.restrictedSpectrum = m := by
  rw [B.restrictedSpectrum_eq_nonvacuum]
  exact hasHamiltonianMassGap_sInf_nonvacuum_eq hGap hmSpectrum

/-- The reconstructed Wightman spectrum condition and relativistic gap descend
to a strictly positive lower spectral edge on `Ω⊥`. -/
theorem explicit_wightman_os_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    0 < m ∧
      B.restrictedSpectrum ⊆ Set.Ici m ∧
      sInf B.restrictedSpectrum = m := by
  have hHamiltonianGap : M.HasMassGap m :=
    explicit_wightman_os_reconstruction_has_mass_gap M hRelGap
  exact ⟨hHamiltonianGap.1,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici B hHamiltonianGap,
    vacuum_orthogonal_restrictedSpectrum_sInf_eq B hHamiltonianGap hmSpectrum⟩

/-- Exact-gap specialization of the physical `Ω⊥` spectral theorem. -/
theorem explicit_wightman_os_vacuum_orthogonal_exact_gap_positive
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum : exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal ∧
      sInf B.restrictedSpectrum = exactGapValueReal := by
  exact explicit_wightman_os_vacuum_orthogonal_spectrum_gap
    M B hRelGap hExactSpectrum

/-- The theorem-level certificate for the route

`OS/Wightman reconstruction → physical Hilbert space → self-adjoint Hamiltonian
→ normalized vacuum Ω → complete sector Ω⊥ → restricted spectrum → Δ > 0`.

The certificate contains Mathlib objects and theorem statements rather than a
terminal readiness marker. -/
structure ExplicitWightmanOSVacuumOrthogonalGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    (m : ℝ) where
  physicalHilbertComplete : CompleteSpace M.H
  vacuumOrthogonalComplete : CompleteSpace M.VacuumOrthogonalHilbert
  hamiltonianSelfAdjoint : IsSelfAdjoint M.hamiltonian
  vacuumNormalized : ‖M.vacuum‖ = 1
  vacuumEnergyZero :
    M.hamiltonian ⟨M.vacuum, M.vacuum_mem_hamiltonianDomain⟩ = 0
  vacuumNotOrthogonal : M.vacuum ∉ M.vacuumOrthogonal
  orthogonalSectorNontrivial :
    ∃ ψ : M.VacuumOrthogonalHilbert, (ψ : M.H) ≠ 0
  pvmNonvacuumRangeOrthogonal :
    ∀ {E : ℝ}, E ∈ B.restrictedSpectrum → ∀ ψ : M.H,
      M.spectralPVM.projection ({E} : Set ℝ) ψ ∈ M.vacuumOrthogonal
  restrictedSpectrumEqNonvacuum :
    B.restrictedSpectrum = M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)
  gapPositive : 0 < m
  restrictedSpectrumLowerBound : B.restrictedSpectrum ⊆ Set.Ici m
  restrictedSpectrumInfimum : sInf B.restrictedSpectrum = m

/-- Construct the full physical-vacuum-sector spectral certificate from the
relativistic mass-gap hypothesis and attainment of the lower edge. -/
def explicitWightmanOSVacuumOrthogonalGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSVacuumOrthogonalGapCertificate M B m := by
  have hHamiltonianGap : M.HasMassGap m :=
    explicit_wightman_os_reconstruction_has_mass_gap M hRelGap
  exact
    { physicalHilbertComplete := M.hilbertCompleteSpace
      vacuumOrthogonalComplete := inferInstance
      hamiltonianSelfAdjoint := M.hamiltonianSelfAdjoint
      vacuumNormalized := M.vacuum_norm
      vacuumEnergyZero := M.vacuumEnergyZero
      vacuumNotOrthogonal :=
        explicit_wightman_os_vacuum_not_mem_vacuumOrthogonal M
      orthogonalSectorNontrivial := B.orthogonalSector_nontrivial
      pvmNonvacuumRangeOrthogonal := B.pvm_nonvacuum_range_orthogonal
      restrictedSpectrumEqNonvacuum := B.restrictedSpectrum_eq_nonvacuum
      gapPositive := hHamiltonianGap.1
      restrictedSpectrumLowerBound :=
        vacuum_orthogonal_restrictedSpectrum_subset_Ici B hHamiltonianGap
      restrictedSpectrumInfimum :=
        vacuum_orthogonal_restrictedSpectrum_sInf_eq
          B hHamiltonianGap hmSpectrum }

end

end MathlibAnalytic
end MGAP4D
