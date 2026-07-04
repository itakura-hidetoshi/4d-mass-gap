import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapAuditFinalIndex
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuumMassGapAuditFinalIndex

/-- Final audit release theorem for the positive-gap existential. -/
theorem release_existsPositiveGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    {A : ContinuumMassGapExternalAuditPacket C O M S P R}
    {Q : ContinuumMassGapAuditCompletionReceipt C O M S P R A}
    (I : ContinuumMassGapAuditFinalIndex C O M S P R A Q) :
    ∃ gap : ℝ, 0 < gap :=
  existsPositiveGap I

/-- Final audit release theorem retaining boundary markers. -/
theorem release_existsPositiveGap_withBoundaries
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    {A : ContinuumMassGapExternalAuditPacket C O M S P R}
    {Q : ContinuumMassGapAuditCompletionReceipt C O M S P R A}
    (I : ContinuumMassGapAuditFinalIndex C O M S P R A Q) :
    (∃ gap : ℝ, 0 < gap) ∧
      R.ledger.separatesClusteringFromSpectralGap ∧
        R.ledger.noUnconditionalClayClaim :=
  ⟨existsPositiveGap I, boundaryMarkers I⟩

/-- Final audit release theorem directly from an audit-completion receipt. -/
theorem release_existsPositiveGap_ofCompletionReceipt
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P)
    (A : ContinuumMassGapExternalAuditPacket C O M S P R)
    (Q : ContinuumMassGapAuditCompletionReceipt C O M S P R A) :
    ∃ gap : ℝ, 0 < gap :=
  release_existsPositiveGap (ofCompletionReceipt C O M S P R A Q)

end ContinuumMassGapAuditFinalIndex

end

end MathlibAnalytic
end MGAP4D
