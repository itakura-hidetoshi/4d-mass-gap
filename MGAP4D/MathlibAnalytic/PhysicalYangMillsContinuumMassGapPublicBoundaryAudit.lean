import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapConditionalTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Audit surface for the public continuum mass-gap route. -/
structure ContinuumMassGapPublicBoundaryAudit
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P)
    (U : ContinuumMassGapPublicSurface C O M S P R) where
  publicSurfaceAvailable : True := trivial
  positiveGapAvailable : 0 < U.gapValue
  continuumConfigurationAvailable : C.configSpace.isContinuumR4GaugeFieldModel
  spectralGapStatementAvailable : O.spectralGapStatement
  separatesClusteringFromSpectralGap : R.ledger.separatesClusteringFromSpectralGap
  noUnconditionalClayClaim : R.ledger.noUnconditionalClayClaim

namespace ContinuumMassGapPublicBoundaryAudit

/-- The audit exposes the positive gap proof. -/
theorem positiveGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    {U : ContinuumMassGapPublicSurface C O M S P R}
    (A : ContinuumMassGapPublicBoundaryAudit C O M S P R U) :
    0 < U.gapValue :=
  A.positiveGapAvailable

/-- The audit exposes the separation marker. -/
theorem separationMarker
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    {U : ContinuumMassGapPublicSurface C O M S P R}
    (A : ContinuumMassGapPublicBoundaryAudit C O M S P R U) :
    R.ledger.separatesClusteringFromSpectralGap :=
  A.separatesClusteringFromSpectralGap

/-- The audit exposes the no-unconditional-claim marker. -/
theorem noClayClaim
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    {U : ContinuumMassGapPublicSurface C O M S P R}
    (A : ContinuumMassGapPublicBoundaryAudit C O M S P R U) :
    R.ledger.noUnconditionalClayClaim :=
  A.noUnconditionalClayClaim

/-- Build the audit surface from a public surface. -/
def ofPublicSurface
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P)
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    ContinuumMassGapPublicBoundaryAudit C O M S P R U :=
  { positiveGapAvailable := U.gapPositive
    continuumConfigurationAvailable := U.continuumConfiguration
    spectralGapStatementAvailable := U.spectralGapStatement
    separatesClusteringFromSpectralGap := U.separatesClusteringFromSpectralGap
    noUnconditionalClayClaim := U.noUnconditionalClayClaim }

end ContinuumMassGapPublicBoundaryAudit

end

end MathlibAnalytic
end MGAP4D
