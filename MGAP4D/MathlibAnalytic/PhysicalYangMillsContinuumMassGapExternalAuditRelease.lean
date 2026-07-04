import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapExternalAuditPacket
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuumMassGapExternalAuditPacket

/-- External audit release theorem for the public positive-gap existential. -/
theorem release_existsPositiveGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (A : ContinuumMassGapExternalAuditPacket C O M S P R) :
    ∃ gap : ℝ, 0 < gap :=
  existsPositiveGap A

/-- External audit release theorem retaining the boundary markers. -/
theorem release_existsPositiveGap_withBoundaries
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (A : ContinuumMassGapExternalAuditPacket C O M S P R) :
    (∃ gap : ℝ, 0 < gap) ∧
      R.ledger.separatesClusteringFromSpectralGap ∧
        R.ledger.noUnconditionalClayClaim :=
  ⟨existsPositiveGap A, boundaryMarkersHeld A⟩

/-- External audit release theorem directly from a route package. -/
theorem release_existsPositiveGap_ofRoutePackage
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P)
    (auditReady : Prop) :
    ∃ gap : ℝ, 0 < gap :=
  release_existsPositiveGap (ofRoutePackage C O M S P R auditReady)

end ContinuumMassGapExternalAuditPacket

end

end MathlibAnalytic
end MGAP4D
