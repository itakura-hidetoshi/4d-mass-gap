import MGAP4D.MathlibAnalytic.ExplicitWightmanOSExactGapPVMOpenSupportCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Recover the pure PVM open-support bridge from a full scalar spectral realization
and the corresponding scalar-support bridge.

The full measurable-set quadratic formula already proves that the union of
scalar-measure supports is exactly the open-neighborhood support of the bounded
PVM.  Therefore the scalar and pure-PVM support identifications are equivalent
once that realization is available.
-/

/-- A scalar-support identification for a full quadratic realization generates
the pure PVM open-support bridge. -/
def ExplicitWightmanOSCanonicalSpectralSupportBridge.toCanonicalPVMOpenSupportBridge
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      M F.toScalarSpectralRealization) :
    ExplicitWightmanOSCanonicalPVMOpenSupportBridge M :=
  { toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge :=
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
    pvmOpenSupport_eq_restrictedSpectrum := by
      rw [← full_scalar_vacuumOrthogonal_support_eq_pvmOpenSupport F]
      exact B.spectralSupport_eq_restrictedSpectrum }

/-- The generated pure-PVM bridge preserves the canonical restricted Hamiltonian
bridge definitionally. -/
@[simp] theorem ExplicitWightmanOSCanonicalSpectralSupportBridge.toCanonicalPVMOpenSupportBridge_hamiltonianBridge
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      M F.toScalarSpectralRealization) :
    (B.toCanonicalPVMOpenSupportBridge F).toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge =
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge := by
  rfl

/-- The scalar support and the generated pure PVM open support are the same
physical spectral set. -/
theorem ExplicitWightmanOSCanonicalSpectralSupportBridge.scalarSupport_eq_pvmOpenSupport
    {M : ExplicitWightmanOSReconstructedModel}
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      M F.toScalarSpectralRealization) :
    M.canonicalVacuumOrthogonalSpectralSupport F.toScalarSpectralRealization =
      M.vacuumOrthogonalPVMOpenSupport :=
  full_scalar_vacuumOrthogonal_support_eq_pvmOpenSupport F

/-- A full scalar realization and scalar-support bridge therefore produce the
continuous-spectrum-compatible exact-gap theorem for the actual PVM support. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support_of_scalar_support
    (M : ExplicitWightmanOSReconstructedModel)
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      M F.toScalarSpectralRealization)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSExactGapPVMOpenSupportProp
      M (B.toCanonicalPVMOpenSupportBridge F) hGap hExactSpectrum := by
  exact explicit_wightman_os_exact_gap_pvm_open_support
    M (B.toCanonicalPVMOpenSupportBridge F) hGap hExactSpectrum

/-- Quadratic PVM countable additivity supplies the required full scalar
realization, so a scalar-support bridge for the constructed measures generates
the pure PVM exact-gap theorem. -/
theorem explicit_wightman_os_quadratic_pvm_exact_gap_open_support
    (M : ExplicitWightmanOSReconstructedModel)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      M A.toScalarSpectralRealization)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSExactGapPVMOpenSupportProp
      M
      (B.toCanonicalPVMOpenSupportBridge
        A.toFullScalarSpectralMeasureRealization)
      hGap hExactSpectrum := by
  exact explicit_wightman_os_exact_gap_pvm_open_support_of_scalar_support
    M A.toFullScalarSpectralMeasureRealization B hGap hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
