import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapPublicRelease
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Receipt for the public route index and its released positive-gap statement. -/
structure ContinuumMassGapPublicReceipt
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) where
  routeIndex : ContinuumMassGapRouteIndex C O M S P R
  releasedPositiveGap : ∃ gap : ℝ, 0 < gap
  releasedPositiveGap_eq :
    releasedPositiveGap =
      ContinuumMassGapRouteIndex.exists_public_positive_gap routeIndex
  boundaryMarkers :
    R.ledger.separatesClusteringFromSpectralGap ∧
      R.ledger.noUnconditionalClayClaim

namespace ContinuumMassGapPublicReceipt

/-- Build the receipt from a route index. -/
def ofRouteIndex
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P)
    (I : ContinuumMassGapRouteIndex C O M S P R) :
    ContinuumMassGapPublicReceipt C O M S P R :=
  { routeIndex := I
    releasedPositiveGap := ContinuumMassGapRouteIndex.exists_public_positive_gap I
    releasedPositiveGap_eq := rfl
    boundaryMarkers :=
      ⟨I.audit.separatesClusteringFromSpectralGap,
        I.audit.noUnconditionalClayClaim⟩ }

/-- Build the receipt directly from a route package. -/
def ofRoutePackage
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) :
    ContinuumMassGapPublicReceipt C O M S P R :=
  ofRouteIndex C O M S P R
    (ContinuumMassGapRouteIndex.ofRoutePackage C O M S P R)

/-- Extract the released positive-gap existential. -/
theorem existsPositiveGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (Q : ContinuumMassGapPublicReceipt C O M S P R) :
    ∃ gap : ℝ, 0 < gap :=
  Q.releasedPositiveGap

/-- Extract the retained route boundary markers. -/
theorem boundaryMarkersHeld
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (Q : ContinuumMassGapPublicReceipt C O M S P R) :
    R.ledger.separatesClusteringFromSpectralGap ∧
      R.ledger.noUnconditionalClayClaim :=
  Q.boundaryMarkers

end ContinuumMassGapPublicReceipt

end

end MathlibAnalytic
end MGAP4D
