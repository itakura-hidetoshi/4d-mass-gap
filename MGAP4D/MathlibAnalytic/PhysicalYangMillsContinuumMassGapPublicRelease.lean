import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapRouteIndex
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuumMassGapRouteIndex

/-- Public release theorem: a route index gives a conditional positive gap value. -/
theorem exists_public_positive_gap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (I : ContinuumMassGapRouteIndex C O M S P R) :
    ∃ gap : ℝ, 0 < gap :=
  ⟨I.indexGapValue, gapPositive I⟩

/-- Public release theorem with the route boundary markers retained. -/
theorem exists_public_positive_gap_with_boundaries
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    {P : ContinuumPositiveMassGapCertificate C O M S}
    {R : ContinuumMassGapRoutePackage C O M S P}
    (I : ContinuumMassGapRouteIndex C O M S P R) :
    (∃ gap : ℝ, 0 < gap) ∧
      R.ledger.separatesClusteringFromSpectralGap ∧
        R.ledger.noUnconditionalClayClaim :=
  ⟨exists_public_positive_gap I,
    I.audit.separatesClusteringFromSpectralGap,
    I.audit.noUnconditionalClayClaim⟩

/-- Build a route index and expose the conditional positive gap from a route
package in one theorem. -/
theorem exists_public_positive_gap_of_route_package
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M)
    (P : ContinuumPositiveMassGapCertificate C O M S)
    (R : ContinuumMassGapRoutePackage C O M S P) :
    ∃ gap : ℝ, 0 < gap :=
  exists_public_positive_gap (ofRoutePackage C O M S P R)

end ContinuumMassGapRouteIndex

end

end MathlibAnalytic
end MGAP4D
