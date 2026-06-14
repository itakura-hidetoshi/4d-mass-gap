import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertReconstructedModel
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact physical certificate for the OS-reconstructed model.  It joins the
positive-time OS completion, the exported explicit Wightman model, the
self-adjoint Hamiltonian restricted to the vacuum-orthogonal sector, and the
exact non-vacuum spectral lower edge. -/
structure EuclideanYangMillsOSPhysicalExactRestrictedGapCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      M.toExplicitModel) where
  reconstruction : EuclideanYangMillsOSPhysicalReconstructionCertificate M
  explicitMassGap : M.toExplicitModel.HasMassGap exactGapValueReal
  restrictedHamiltonianGap :
    ExplicitWightmanOSCanonicalRestrictedHamiltonianGapCertificate
      M.toExplicitModel B exactGapValueReal

/-- Assemble the exact restricted-Hamiltonian certificate from a relativistic
exact-gap witness and membership of the exact lower edge in the Hamiltonian
spectrum. -/
def euclideanYangMillsOSPhysicalExactRestrictedGapCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap
        M.toExplicitModel.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.toExplicitModel.hamiltonianEnergySpectrum) :
    EuclideanYangMillsOSPhysicalExactRestrictedGapCertificate M B :=
  { reconstruction := euclideanYangMillsOSPhysicalReconstructionCertificate M
    explicitMassGap :=
      explicit_wightman_os_reconstruction_has_mass_gap M.toExplicitModel hRelGap
    restrictedHamiltonianGap :=
      explicitWightmanOSCanonicalRestrictedHamiltonianGapCertificate
        M.toExplicitModel B hRelGap hExactSpectrum }

/-- The canonical vacuum-orthogonal Hamiltonian of the OS-reconstructed model is
self-adjoint once the exact restricted-gap certificate has been supplied. -/
theorem os_physical_exact_restricted_hamiltonian_selfAdjoint
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      M.toExplicitModel}
    (C : EuclideanYangMillsOSPhysicalExactRestrictedGapCertificate M B) :
    IsSelfAdjoint M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian :=
  C.restrictedHamiltonianGap.operatorSelfAdjoint

/-- Its actual intersection domain is dense in the vacuum-orthogonal Hilbert
space. -/
theorem os_physical_exact_restricted_hamiltonian_dense_domain
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      M.toExplicitModel}
    (C : EuclideanYangMillsOSPhysicalExactRestrictedGapCertificate M B) :
    Dense
      ((M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain :
        Set M.toExplicitModel.VacuumOrthogonalHilbert)) :=
  C.restrictedHamiltonianGap.operatorDomainDense

/-- The canonical vacuum-orthogonal Hamiltonian is closed. -/
theorem os_physical_exact_restricted_hamiltonian_closed
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      M.toExplicitModel}
    (C : EuclideanYangMillsOSPhysicalExactRestrictedGapCertificate M B) :
    LinearPMap.IsClosed
      M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian :=
  C.restrictedHamiltonianGap.operatorClosed

/-- The non-vacuum spectrum is bounded below by the normalized exact-gap
carrier. -/
theorem os_physical_exact_restricted_spectrum_lower_bound
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      M.toExplicitModel}
    (C : EuclideanYangMillsOSPhysicalExactRestrictedGapCertificate M B) :
    B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal :=
  C.restrictedHamiltonianGap.spectrumLowerBound

/-- The infimum of the actual non-vacuum restricted spectrum is exactly the
normalized exact-gap carrier. -/
theorem os_physical_exact_restricted_spectrum_infimum
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      M.toExplicitModel}
    (C : EuclideanYangMillsOSPhysicalExactRestrictedGapCertificate M B) :
    sInf B.restrictedSpectrum = exactGapValueReal :=
  C.restrictedHamiltonianGap.spectrumInfimum

end

end MathlibAnalytic
end MGAP4D
