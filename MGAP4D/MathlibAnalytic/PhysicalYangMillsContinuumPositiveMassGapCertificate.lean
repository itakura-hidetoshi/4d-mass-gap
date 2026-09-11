import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumSpectralGapCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A positive mass-gap certificate extracted from a Hamiltonian spectral-gap
certificate. -/
structure ContinuumPositiveMassGapCertificate
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M) where
  massGapValue : ℝ
  massGapPositive : 0 < massGapValue
  agreesWithSpectralGap : massGapValue = S.gapValue
  spectralGapStatement : O.spectralGapStatement

namespace ContinuumPositiveMassGapCertificate

/-- The certified positive mass-gap value as a positive real subtype. -/
def positiveMassGapValue
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    (P : ContinuumPositiveMassGapCertificate C O M S) :
    { gap : ℝ // 0 < gap } :=
  ⟨P.massGapValue, P.massGapPositive⟩

/-- The mass-gap value agrees with the spectral-gap value. -/
theorem value_eq_spectralGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    (P : ContinuumPositiveMassGapCertificate C O M S) :
    P.massGapValue = S.gapValue :=
  P.agreesWithSpectralGap

/-- The mass-gap value is positive. -/
theorem positive
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    {S : ContinuumHamiltonianSpectralGapCertificate C O M}
    (P : ContinuumPositiveMassGapCertificate C O M S) :
    0 < P.massGapValue :=
  P.massGapPositive

/-- Build a positive mass-gap certificate from a spectral-gap certificate. -/
def ofSpectralGap
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (S : ContinuumHamiltonianSpectralGapCertificate C O M) :
    ContinuumPositiveMassGapCertificate C O M S :=
  { massGapValue := S.gapValue
    massGapPositive := S.gapPositive
    agreesWithSpectralGap := rfl
    spectralGapStatement := S.spectralGapStatement }

end ContinuumPositiveMassGapCertificate

end

end MathlibAnalytic
end MGAP4D
