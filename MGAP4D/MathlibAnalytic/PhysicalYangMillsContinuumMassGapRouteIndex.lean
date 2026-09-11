import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapPublicBoundaryAudit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Index object bundling the public surface and its boundary audit. -/
structure ContinuumMassGapRouteIndex
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) where
  publicSurface : ContinuumMassGapPublicSurface C O M S P R
  audit : ContinuumMassGapPublicBoundaryAudit C O M S P R publicSurface
  indexGapValue : ℝ
  indexGapValue_eq_public : indexGapValue = publicSurface.gapValue

namespace ContinuumMassGapRouteIndex

/-- The indexed gap value is positive. -/
theorem gapPositive
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (I : ContinuumMassGapRouteIndex C O M S P R) :
    0 < I.indexGapValue := by
  rw [I.indexGapValue_eq_public]
  exact I.publicSurface.gapPositive

/-- The route index exposes the audit no-claim marker. -/
theorem noClayClaim
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (I : ContinuumMassGapRouteIndex C O M S P R) :
    R.ledger.noUnconditionalClayClaim :=
  I.audit.noUnconditionalClayClaim

/-- Build the route index from a route package. -/
def ofRoutePackage
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) :
    ContinuumMassGapRouteIndex C O M S P R :=
  let U := ContinuumMassGapPublicSurface.ofRoutePackage C O M S P R
  { publicSurface := U
    audit := ContinuumMassGapPublicBoundaryAudit.ofPublicSurface C O M S P R U
    indexGapValue := U.gapValue
    indexGapValue_eq_public := rfl }

end ContinuumMassGapRouteIndex

end

end MathlibAnalytic
end MGAP4D
