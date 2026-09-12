import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapPublicReceipt
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- External audit packet for the public route receipt. -/
structure ContinuumMassGapExternalAuditPacket
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) where
  receipt : ContinuumMassGapPublicReceipt C O M S P R
  positiveGapReleased : ∃ gap : ℝ, 0 < gap
  positiveGapReleased_eq :
    positiveGapReleased = ContinuumMassGapPublicReceipt.existsPositiveGap receipt
  boundaryMarkersReleased :
    R.ledger.separatesClusteringFromSpectralGap ∧
      R.ledger.noUnconditionalClayClaim
  auditReady : Prop

namespace ContinuumMassGapExternalAuditPacket

/-- Build an audit packet from a public receipt. -/
def ofReceipt
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P)
    (Q : ContinuumMassGapPublicReceipt C O M S P R)
    (auditReady : Prop) :
    ContinuumMassGapExternalAuditPacket C O M S P R :=
  { receipt := Q
    positiveGapReleased := ContinuumMassGapPublicReceipt.existsPositiveGap Q
    positiveGapReleased_eq := rfl
    boundaryMarkersReleased := ContinuumMassGapPublicReceipt.boundaryMarkersHeld Q
    auditReady := auditReady }

/-- Build an audit packet directly from a route package. -/
def ofRoutePackage
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P)
    (auditReady : Prop) :
    ContinuumMassGapExternalAuditPacket C O M S P R :=
  ofReceipt C O M S P R
    (ContinuumMassGapPublicReceipt.ofRoutePackage C O M S P R)
    auditReady

/-- Extract the released positive-gap existential from the packet. -/
theorem existsPositiveGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (A : ContinuumMassGapExternalAuditPacket C O M S P R) :
    ∃ gap : ℝ, 0 < gap :=
  A.positiveGapReleased

/-- Extract the retained boundary markers from the packet. -/
theorem boundaryMarkersHeld
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (A : ContinuumMassGapExternalAuditPacket C O M S P R) :
    R.ledger.separatesClusteringFromSpectralGap ∧
      R.ledger.noUnconditionalClayClaim :=
  A.boundaryMarkersReleased

end ContinuumMassGapExternalAuditPacket

end

end MathlibAnalytic
end MGAP4D
