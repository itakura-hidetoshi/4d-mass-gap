import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapPublicSurface
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuumMassGapPublicSurface

/-- A public surface gives a conditional positive gap value. -/
theorem exists_positive_gap_value
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    ∃ gap : ℝ, 0 < gap :=
  ⟨U.gapValue, U.gapPositive⟩

/-- A public surface gives a conditional positive gap value agreeing with the
route package. -/
theorem exists_positive_gap_value_eq_route
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    ∃ gap : ℝ,
      gap = ContinuumMassGapRoutePackage.massGapValue R ∧ 0 < gap :=
  ⟨U.gapValue, U.gapValue_eq_route, U.gapPositive⟩

/-- A public surface gives the continuum configuration proof and the spectral-gap
statement together. -/
theorem continuum_configuration_and_spectral_gap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    C.configSpace.isContinuumR4GaugeFieldModel ∧ O.spectralGapStatement :=
  ⟨U.continuumConfiguration, U.spectralGapStatement⟩

/-- A public surface retains the two route-boundary markers. -/
theorem route_boundary_markers
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (U : ContinuumMassGapPublicSurface C O M S P R) :
    R.ledger.separatesClusteringFromSpectralGap ∧
      R.ledger.noUnconditionalClayClaim :=
  ⟨U.separatesClusteringFromSpectralGap, U.noUnconditionalClayClaim⟩

end ContinuumMassGapPublicSurface

end

end MathlibAnalytic
end MGAP4D
