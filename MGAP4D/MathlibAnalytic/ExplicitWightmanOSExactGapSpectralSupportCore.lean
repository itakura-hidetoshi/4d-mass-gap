import MGAP4D.MathlibAnalytic.ExplicitWightmanOSExactGapSpectralCore
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianSpectralSupport

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Connect the explicit exact-gap spectral core to the scalar spectral support of the
actual vacuum-orthogonal Hamiltonian sector.

This route does not require the exact threshold to be a singleton PVM eigenvalue.
The support bridge identifies the union of scalar-measure supports with the full
non-vacuum Hamiltonian spectrum, including continuous spectral support.
-/

/-- The scalar spectral support of the physical vacuum-orthogonal sector is the
non-vacuum spectrum of the exact-gap core generated from the same explicit model. -/
theorem ExplicitWightmanOSCanonicalSpectralSupportBridge.support_eq_exactGapCore_nonvacuum
    {M : ExplicitWightmanOSReconstructedModel}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization M}
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    M.canonicalVacuumOrthogonalSpectralSupport R =
      (M.toExactGapSpectralCore hGap hExactSpectrum).energySpectrum \
        ({0} : Set ℝ) := by
  rw [B.spectralSupport_eq_restrictedSpectrum]
  exact B.restrictedSpectrum_eq_nonvacuum

/-- Threshold attainment in the Hamiltonian spectrum places the exact gap in the
full scalar spectral support, without requiring a singleton eigenspace. -/
theorem ExplicitWightmanOSCanonicalSpectralSupportBridge.exactGap_mem_support
    {M : ExplicitWightmanOSReconstructedModel}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization M}
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    exactGapValueReal ∈ M.canonicalVacuumOrthogonalSpectralSupport R := by
  rw [B.support_eq_exactGapCore_nonvacuum hGap hExactSpectrum]
  exact ⟨hExactSpectrum, by simpa using (ne_of_gt hGap.1)⟩

/-- The exact gap is the least point of the full physical scalar spectral support. -/
theorem ExplicitWightmanOSCanonicalSpectralSupportBridge.exactGap_isLeast_support
    {M : ExplicitWightmanOSReconstructedModel}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization M}
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    IsLeast (M.canonicalVacuumOrthogonalSpectralSupport R)
      exactGapValueReal := by
  refine ⟨B.exactGap_mem_support hGap hExactSpectrum, ?_⟩
  intro energy hEnergy
  exact
    (canonical_vacuum_orthogonal_spectralSupport_lower_bound B hGap)
      hEnergy

/-- The full scalar spectral support and the generated exact-gap core have the
same exact lower edge. -/
theorem ExplicitWightmanOSCanonicalSpectralSupportBridge.support_sInf_eq_exactGap
    {M : ExplicitWightmanOSReconstructedModel}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization M}
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    sInf (M.canonicalVacuumOrthogonalSpectralSupport R) =
      exactGapValueReal := by
  exact canonical_vacuum_orthogonal_spectralSupport_sInf_eq
    B hGap hExactSpectrum

/-- Compact physical statement connecting the actual self-adjoint Hamiltonian,
the exact-gap core, and the full scalar spectral support. -/
abbrev ExplicitWightmanOSExactGapSpectralSupportProp
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) : Prop :=
  let core := M.toExactGapSpectralCore hGap hExactSpectrum
  core.hamiltonianSelfAdjoint ∧
    M.canonicalVacuumOrthogonalSpectralSupport R =
      core.energySpectrum \ ({0} : Set ℝ) ∧
    0 ∉ M.canonicalVacuumOrthogonalSpectralSupport R ∧
    IsLeast (M.canonicalVacuumOrthogonalSpectralSupport R)
      exactGapValueReal ∧
    sInf (M.canonicalVacuumOrthogonalSpectralSupport R) =
      exactGapValueReal

/-- The explicit exact-gap core and full scalar spectral support satisfy the
physical support-level gap theorem simultaneously. -/
theorem explicit_wightman_os_exact_gap_spectral_support
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSExactGapSpectralSupportProp
      M R B hGap hExactSpectrum := by
  exact ⟨
    M.toExactGapSpectralCore_selfAdjoint hGap hExactSpectrum,
    B.support_eq_exactGapCore_nonvacuum hGap hExactSpectrum,
    canonical_vacuum_orthogonal_spectralSupport_zero_not_mem B,
    B.exactGap_isLeast_support hGap hExactSpectrum,
    B.support_sInf_eq_exactGap hGap hExactSpectrum⟩

end

end MathlibAnalytic
end MGAP4D
