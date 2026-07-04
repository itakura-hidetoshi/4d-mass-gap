import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapBoundaryLedger
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A final package tying together a positive mass-gap candidate and the boundary
ledger that records the remaining scope conditions. -/
structure ContinuumMassGapRoutePackage
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S) where
  candidate : ContinuumYangMillsMassGapCandidateCertificate C O M S P
  ledger : ContinuumMassGapBoundaryLedger C O M
  separatesClusteringFromSpectralGap : ledger.separatesClusteringFromSpectralGap
  noUnconditionalClayClaim : ledger.noUnconditionalClayClaim

namespace ContinuumMassGapRoutePackage

/-- Extract the positive mass-gap value. -/
def massGapValue
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (_R : ContinuumMassGapRoutePackage C O M S P) : ℝ :=
  P.massGapValue

/-- The packaged mass-gap value is positive. -/
theorem massGapPositive
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (R : ContinuumMassGapRoutePackage C O M S P) :
    0 < massGapValue R :=
  R.candidate.positiveMassGap

/-- The package includes continuum configuration-space construction. -/
theorem continuumConfiguration
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (R : ContinuumMassGapRoutePackage C O M S P) :
    C.configSpace.isContinuumR4GaugeFieldModel :=
  R.candidate.continuumConfigurationSpaceConstructed

/-- The package includes the spectral-gap statement. -/
theorem spectralGapStatement
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (R : ContinuumMassGapRoutePackage C O M S P) :
    O.spectralGapStatement :=
  R.candidate.spectralGapStatement

/-- The package records separation between clustering and spectral-gap steps. -/
theorem separatesClustering
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (R : ContinuumMassGapRoutePackage C O M S P) :
    R.ledger.separatesClusteringFromSpectralGap :=
  R.separatesClusteringFromSpectralGap

/-- The package records that no unconditional Clay-claim is introduced by the
routing layer itself. -/
theorem noClayClaim
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    (R : ContinuumMassGapRoutePackage C O M S P) :
    R.ledger.noUnconditionalClayClaim :=
  R.noUnconditionalClayClaim

/-- Build a route package from a candidate, a ledger, and the two boundary proofs. -/
def ofCandidateAndLedger
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (candidate : ContinuumYangMillsMassGapCandidateCertificate C O M S P)
    (ledger : ContinuumMassGapBoundaryLedger C O M)
    (hSeparate : ledger.separatesClusteringFromSpectralGap)
    (hNoClay : ledger.noUnconditionalClayClaim) :
    ContinuumMassGapRoutePackage C O M S P :=
  { candidate := candidate
    ledger := ledger
    separatesClusteringFromSpectralGap := hSeparate
    noUnconditionalClayClaim := hNoClay }

end ContinuumMassGapRoutePackage

end

end MathlibAnalytic
end MGAP4D
