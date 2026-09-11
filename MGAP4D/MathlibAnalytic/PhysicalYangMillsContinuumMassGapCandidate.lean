import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumPositiveMassGapCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A routed continuum mass-gap candidate certificate.

The certificate bundles a positive mass-gap certificate with the continuum
construction and OS-route proof terms on which it depends. -/
structure ContinuumYangMillsMassGapCandidateCertificate
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S) where
  continuumConfigurationSpaceConstructed : C.configSpace.isContinuumR4GaugeFieldModel
  gaugeSymmetryImplemented : C.configSpace.hasGaugeSymmetry
  reflectionPositivity : C.axioms.reflectionPositivity
  osHilbertSpace : Type
  osHilbertSpace_eq : osHilbertSpace = O.HilbertSpaceCarrier
  positiveMassGap : 0 < P.massGapValue
  spectralGapStatement : O.spectralGapStatement

namespace ContinuumYangMillsMassGapCandidateCertificate

/-- Extract the certified positive mass-gap value. -/
def massGapValue
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (_G : ContinuumYangMillsMassGapCandidateCertificate C O M S P) : ℝ :=
  P.massGapValue

/-- Positivity of the certified mass-gap value. -/
theorem massGapPositive
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (G : ContinuumYangMillsMassGapCandidateCertificate C O M S P) :
    0 < massGapValue G :=
  G.positiveMassGap

/-- The candidate includes the continuum configuration-space construction proof. -/
theorem continuumConfiguration
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (G : ContinuumYangMillsMassGapCandidateCertificate C O M S P) :
    C.configSpace.isContinuumR4GaugeFieldModel :=
  G.continuumConfigurationSpaceConstructed

/-- The candidate includes reflection positivity. -/
theorem reflectionPositive
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (G : ContinuumYangMillsMassGapCandidateCertificate C O M S P) :
    C.axioms.reflectionPositivity :=
  G.reflectionPositivity

/-- Build a candidate from the continuum certificate, OS interface, handoff, and
positive mass-gap certificate. -/
def ofPositiveMassGap
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S) :
    ContinuumYangMillsMassGapCandidateCertificate C O M S P :=
  { continuumConfigurationSpaceConstructed := C.axioms.continuumConfigurationSpaceConstructed
    gaugeSymmetryImplemented := C.axioms.gaugeSymmetryImplemented
    reflectionPositivity := O.reflectionPositivityDischarged
    osHilbertSpace := O.HilbertSpaceCarrier
    osHilbertSpace_eq := rfl
    positiveMassGap := P.massGapPositive
    spectralGapStatement := P.spectralGapStatement }

end ContinuumYangMillsMassGapCandidateCertificate

end

end MathlibAnalytic
end MGAP4D
