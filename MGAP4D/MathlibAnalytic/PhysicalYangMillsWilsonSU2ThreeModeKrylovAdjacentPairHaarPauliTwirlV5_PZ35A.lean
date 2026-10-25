import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourEdgeSchurDescentV5_PZ35
import Mathlib.Tactic

/-!
# P4-Q2-PZ35A — exact finite Pauli/quaternion matrix twirl for actual SU(2)

Schur's orthogonality is not imported from Mathlib's finite-GROUP
character orthogonality (which would be inapplicable to compact SU(2)).
Instead we start its compact Haar proof with a finite, purely ALGEBRAIC
2-by-2 matrix identity. Four fixed genuine quaternionic Pauli matrices
constitute a trace-dual basis of the full complex 2-by-2 matrix algebra:
  2 U = tr(U) I - tr(J U) J - tr(K U) K - tr(L U) L.
There is no assumption on U. This identity is the algebraic part
of Haar twirling; the separate proof of Haar translation invariance
and its genuine four-link tensorization are subsequent stages.

No alternative Wilson action, independent posterior, new axiom,
sorry/admit/native_decide or hidden Schur premise.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Identity quaternion in the actual complex 2x2 matrix algebra. -/
def p4Q2PZ35A_pauliQ0 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, 1]

/-- Real quaternion generator J (a unitary determinant-one matrix). -/
def p4Q2PZ35A_pauliQ1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), -1; 1, 0]

/-- Imaginary diagonal quaternion generator K. -/
def p4Q2PZ35A_pauliQ2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Complex.I : ℂ), 0; 0, -Complex.I]

/-- Third quaternion generator L = J*K. -/
def p4Q2PZ35A_pauliQ3 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), Complex.I; Complex.I, 0]

/-- Exact trace-dual decomposition in the complex 2x2 matrix algebra.
This finite algebraic step needs NO Haar, no Schur theorem, and no
assumption that the matrix U is special unitary. -/
theorem p4Q2PZ35A_pauliTraceDecomposition
    (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (2 : ℂ) • U =
      (Matrix.trace (p4Q2PZ35A_pauliQ0 * U)) • p4Q2PZ35A_pauliQ0 -
      (Matrix.trace (p4Q2PZ35A_pauliQ1 * U)) • p4Q2PZ35A_pauliQ1 -
      (Matrix.trace (p4Q2PZ35A_pauliQ2 * U)) • p4Q2PZ35A_pauliQ2 -
      (Matrix.trace (p4Q2PZ35A_pauliQ3 * U)) • p4Q2PZ35A_pauliQ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
      p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3,
      Matrix.trace_fin_two, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35A_pauliTraceDecomposition
