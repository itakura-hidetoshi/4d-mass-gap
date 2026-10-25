import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionRealTraceV5_PZ35D
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D2 — complex Pauli trace duality, with genuine real SU(2) descent

No Schur representation axiom: apply a trace pairing to the already
Lean-proved PZ35A 2x2 Pauli matrix decomposition. This is the
algebraic four-term polarization necessary for the genuine
SU(2) quaternion-orbit character identity.

SU(2) Wilson's ORIGINAL real character is proved equal, after
embedding in ℂ, to one half of the genuine complex matrix trace
by the unconditional PZ35D real-trace theorem.

No alternate Haar, independence assumption, new axiom, sorry,
admit, native_decide or change to original Wilson action.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

/-- Complex trace pairing with the unconditional Pauli decomposition:
the four coefficient contractions equal twice the true trace pairing.
This holds for ALL complex 2×2 matrices, not only SU(2). -/
theorem p4Q2PZ35D2_complexPauliTracePair (A C : Mat) :
    Matrix.trace (p4Q2PZ35A_pauliQ0 * A) *
        Matrix.trace (C * p4Q2PZ35A_pauliQ0) -
      Matrix.trace (p4Q2PZ35A_pauliQ1 * A) *
        Matrix.trace (C * p4Q2PZ35A_pauliQ1) -
      Matrix.trace (p4Q2PZ35A_pauliQ2 * A) *
        Matrix.trace (C * p4Q2PZ35A_pauliQ2) -
      Matrix.trace (p4Q2PZ35A_pauliQ3 * A) *
        Matrix.trace (C * p4Q2PZ35A_pauliQ3) =
      2 * Matrix.trace (C * A) := by
  have h :=
    congrArg (fun X : Mat => Matrix.trace (C * X))
      (p4Q2PZ35A_pauliTraceDecomposition A)
  simpa only [mul_sub, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] using h.symm

/-- The original SU(2) real Wilson character is literally half
the complex 2x2 trace, and that trace is real by PZ35D. -/
theorem p4Q2PZ35D2_originalCharacter_complex_coe (g : G) :
    ((p4Q2PZ35C_originalOneLinkCharacter g : ℝ) : ℂ) =
      Matrix.trace (g : Mat) / 2 := by
  change (↑(1 - (1 - (Matrix.trace (g : Mat)).re / (2 : ℝ))) : ℂ) =
    Matrix.trace (g : Mat) / 2
  push_cast
  rw [p4Q2PZ35D_SU2_trace_eq_real g]
  ring

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D2_complexPauliTracePair
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D2_originalCharacter_complex_coe
