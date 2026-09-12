import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapRoutePackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Public surface for the routed continuum mass-gap candidate.

This surface exposes a positive gap value and the route boundary markers without
collapsing the route into an unconditional Clay statement. -/
structure ContinuumMassGapPublicSurface
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) where
  gapValue : ℝ
  gapPositive : 0 < gapValue
  gapValue_eq_route : gapValue = ContinuumMassGapRoutePackage.massGapValue R
  continuumConfiguration : C.configSpace.isContinuumR4GaugeFieldModel
  spectralGapStatement : O.spectralGapStatement
  separatesClusteringFromSpectralGap : R.ledger.separatesClusteringFromSpectralGap
  noUnconditionalClayClaim : R.ledger.noUnconditionalClayClaim

namespace ContinuumMassGapPublicSurface

/-- Extract the positive mass-gap value as a positive real subtype. -/
def positiveGapValue
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    { gap : ℝ // 0 < gap } :=
  ⟨U.gapValue, U.gapPositive⟩

/-- The public-surface gap agrees with the route-package gap. -/
theorem gap_eq_route
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    U.gapValue = ContinuumMassGapRoutePackage.massGapValue R :=
  U.gapValue_eq_route

/-- The public surface carries the spectral-gap statement. -/
theorem spectralGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    O.spectralGapStatement :=
  U.spectralGapStatement

/-- Build the public surface from a route package. -/
def ofRoutePackage
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) :
    ContinuumMassGapPublicSurface C O M S P R :=
  { gapValue := ContinuumMassGapRoutePackage.massGapValue R
    gapPositive := ContinuumMassGapRoutePackage.massGapPositive R
    gapValue_eq_route := rfl
    continuumConfiguration := ContinuumMassGapRoutePackage.continuumConfiguration R
    spectralGapStatement := ContinuumMassGapRoutePackage.spectralGapStatement R
    separatesClusteringFromSpectralGap := R.separatesClusteringFromSpectralGap
    noUnconditionalClayClaim := R.noUnconditionalClayClaim }

end ContinuumMassGapPublicSurface

end

end MathlibAnalytic
end MGAP4D
