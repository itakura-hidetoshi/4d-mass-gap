import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapCandidate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A boundary ledger for the continuum mass-gap route.

It records which high-level proof obligations are represented by certificates in
this route and which boundary conditions remain visible. -/
structure ContinuumMassGapBoundaryLedger
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O) where
  hasContinuumConstructionCertificate : C.configSpace.isContinuumR4GaugeFieldModel
  hasGaugeSymmetryCertificate : C.configSpace.hasGaugeSymmetry
  hasReflectionPositivityCertificate : C.axioms.reflectionPositivity
  hasOSInterface : True := trivial
  hasHamiltonianHandoff : O.hamiltonianAvailable
  hasSpectralGapStatement : O.spectralGapStatement
  hasPositiveGapObligation : M.positiveGapObligation
  separatesClusteringFromSpectralGap : Prop
  noUnconditionalClayClaim : Prop

namespace ContinuumMassGapBoundaryLedger

/-- The ledger exposes continuum construction as a proof term. -/
theorem continuumConstruction
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    (L : ContinuumMassGapBoundaryLedger C O M) :
    C.configSpace.isContinuumR4GaugeFieldModel :=
  L.hasContinuumConstructionCertificate

/-- The ledger exposes reflection positivity as a proof term. -/
theorem reflectionPositivity
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    (L : ContinuumMassGapBoundaryLedger C O M) :
    C.axioms.reflectionPositivity :=
  L.hasReflectionPositivityCertificate

/-- The ledger exposes the spectral-gap statement as a proof term. -/
theorem spectralGapStatement
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    (L : ContinuumMassGapBoundaryLedger C O M) :
    O.spectralGapStatement :=
  L.hasSpectralGapStatement

/-- Build the ledger from the continuum certificate, OS interface, and handoff. -/
def ofHandoff
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (separatesClusteringFromSpectralGap : Prop)
    (noUnconditionalClayClaim : Prop) :
    ContinuumMassGapBoundaryLedger C O M :=
  { hasContinuumConstructionCertificate := C.axioms.continuumConfigurationSpaceConstructed
    hasGaugeSymmetryCertificate := C.axioms.gaugeSymmetryImplemented
    hasReflectionPositivityCertificate := O.reflectionPositivityDischarged
    hasHamiltonianHandoff := M.hamiltonianDischarged
    hasSpectralGapStatement := M.spectralGapStatementDischarged
    hasPositiveGapObligation := M.positiveGapObligation
    separatesClusteringFromSpectralGap := separatesClusteringFromSpectralGap
    noUnconditionalClayClaim := noUnconditionalClayClaim }

end ContinuumMassGapBoundaryLedger

end

end MathlibAnalytic
end MGAP4D
