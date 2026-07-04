import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumMassGapHandoff
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A conditional Hamiltonian spectral-gap certificate over a continuum OS
interface and mass-gap handoff. -/
structure ContinuumHamiltonianSpectralGapCertificate
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O) where
  gapValue : ℝ
  gapPositive : 0 < gapValue
  hamiltonianAvailable : O.hamiltonianAvailable
  fieldOperatorMapAvailable : O.fieldOperatorMapAvailable
  vacuumAvailable : O.vacuumAvailable
  spectralGapStatement : O.spectralGapStatement
  positiveGapDischarged : M.positiveGapObligation

namespace ContinuumHamiltonianSpectralGapCertificate

/-- Extract the positive real gap value. -/
def positiveGapValue
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    (S : ContinuumHamiltonianSpectralGapCertificate C O M) :
    { gap : ℝ // 0 < gap } :=
  ⟨S.gapValue, S.gapPositive⟩

/-- The Hamiltonian availability proof. -/
theorem hamiltonian
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    (S : ContinuumHamiltonianSpectralGapCertificate C O M) :
    O.hamiltonianAvailable :=
  S.hamiltonianAvailable

/-- The spectral-gap statement proof. -/
theorem spectralGap
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    (S : ContinuumHamiltonianSpectralGapCertificate C O M) :
    O.spectralGapStatement :=
  S.spectralGapStatement

/-- Positivity of the chosen gap value. -/
theorem positive
    {C : ContinuumYangMillsConstructionCertificate}
    {O : ContinuumOSReconstructionInterface C}
    {M : ContinuumMassGapHandoffInterface C O}
    (S : ContinuumHamiltonianSpectralGapCertificate C O M) :
    0 < S.gapValue :=
  S.gapPositive

/-- Build the spectral-gap certificate from the proof terms named by the handoff. -/
def ofHandoff
    (C : ContinuumYangMillsConstructionCertificate)
    (O : ContinuumOSReconstructionInterface C)
    (M : ContinuumMassGapHandoffInterface C O)
    (gapValue : ℝ)
    (gapPositive : 0 < gapValue)
    (hPositiveGap : M.positiveGapObligation) :
    ContinuumHamiltonianSpectralGapCertificate C O M :=
  { gapValue := gapValue
    gapPositive := gapPositive
    hamiltonianAvailable := M.hamiltonianDischarged
    fieldOperatorMapAvailable := M.fieldOperatorMapDischarged
    vacuumAvailable := M.vacuumDischarged
    spectralGapStatement := M.spectralGapStatementDischarged
    positiveGapDischarged := hPositiveGap }

end ContinuumHamiltonianSpectralGapCertificate

end

end MathlibAnalytic
end MGAP4D
