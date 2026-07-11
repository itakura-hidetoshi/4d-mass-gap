import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology

/-- A concrete sequence of physical PVM-support energies converging to the gap
produces support points arbitrarily close above the gap.

This is the sequential form naturally supplied by finite-volume or scale-indexed
approximations. -/
theorem pvmOpenSupport_arbitrarily_close_above_of_tendsto
    {M : ExplicitWightmanOSReconstructedModel}
    (energy : ℕ → ℝ)
    (hEnergy : ∀ n : ℕ, energy n ∈ M.vacuumOrthogonalPVMOpenSupport)
    (hTendsto : Tendsto energy atTop (nhds exactGapValueReal)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ E ∈ M.vacuumOrthogonalPVMOpenSupport,
        E < exactGapValueReal + ε := by
  intro ε hε
  have hNeighborhood :
      Set.Iio (exactGapValueReal + ε) ∈ nhds exactGapValueReal :=
    Set.Iio_mem_nhds (by linarith)
  have hEventually :
      ∀ᶠ n : ℕ in atTop, energy n < exactGapValueReal + ε :=
    hTendsto.eventually hNeighborhood
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hEventually
  exact ⟨energy n, hEnergy n, hn⟩

/-- The same sequence identifies the support infimum with the exact gap once the
relativistic lower bound is available. -/
theorem pvmOpenSupport_sInf_eq_exactGap_of_tendsto
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (energy : ℕ → ℝ)
    (hEnergy : ∀ n : ℕ, energy n ∈ M.vacuumOrthogonalPVMOpenSupport)
    (hTendsto : Tendsto energy atTop (nhds exactGapValueReal)) :
    sInf M.vacuumOrthogonalPVMOpenSupport = exactGapValueReal := by
  have hGap : M.HasMassGap exactGapValueReal :=
    explicit_wightman_os_reconstruction_has_mass_gap M hRelGap
  have hLower :
      M.vacuumOrthogonalPVMOpenSupport ⊆ Set.Ici exactGapValueReal := by
    rw [B.pvmOpenSupport_eq_restrictedSpectrum]
    exact vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
      hGap
  exact real_sInf_eq_of_subset_Ici_of_arbitrarily_close_above
    hLower
    (pvmOpenSupport_arbitrarily_close_above_of_tendsto
      energy hEnergy hTendsto)

/-- A scale-indexed support-energy sequence closes the remaining support-sharpness
input of the embedded finite-volume transfer endpoint. -/
theorem EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer.sharp_support_real_resolvent_of_tendsto
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (V : EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer T)
    (hMass : V.mass = exactGapValueReal)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (energy : ℕ → ℝ)
    (hEnergy :
      ∀ n : ℕ,
        energy n ∈ M.toExplicitModel.vacuumOrthogonalPVMOpenSupport)
    (hTendsto : Tendsto energy atTop (nhds exactGapValueReal)) :
    EuclideanYangMillsOSPhysicalGeneratorSharpPVMOpenSupportRealResolventProp T := by
  apply V.sharp_support_real_resolvent T G hMass B hRelGap
  exact pvmOpenSupport_arbitrarily_close_above_of_tendsto
    energy hEnergy hTendsto

end

end MathlibAnalytic
end MGAP4D
