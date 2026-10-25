import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPauliTwirlV5_PZ35A
import Mathlib.Tactic

/-!
# P4-Q2-PZ35B — the quaternionic finite twirl is genuinely inside SU(2)

PZ35A established a trace-dual identity for every complex two-by-two matrix.
Here we verify directly, without using finite-group Haar or replacing the
original compact SU(2) Wilson model, that all four quaternionic matrices
in that identity are ACTUAL elements of SU(2).

This file supplies the group carriers and exact matrix representatives
needed to transport the PZ35A identity under genuine normalized compact
SU(2) Haar left translation. The subsequent Haar integral contraction is
NOT claimed in this file.

No new axiom, sorry/admit/native_decide or independent posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

/-- The real quaternion J satisfies both exact SU(2) defining conditions. -/
theorem p4Q2PZ35B_pauliQ1_mem_SU2 :
    p4Q2PZ35A_pauliQ1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [p4Q2PZ35A_pauliQ1, Matrix.vecMul, dotProduct]
  · simp [p4Q2PZ35A_pauliQ1, Matrix.det_fin_two]

/-- Imaginary quaternion K has unitary adjoint and determinant one. -/
theorem p4Q2PZ35B_pauliQ2_mem_SU2 :
    p4Q2PZ35A_pauliQ2 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [p4Q2PZ35A_pauliQ2, Matrix.vecMul, dotProduct]
  · simp [p4Q2PZ35A_pauliQ2, Matrix.det_fin_two]

/-- Genuine SU(2) quaternion J, with matrix exactly the PZ35A J. -/
def p4Q2PZ35B_quaternionJ : G :=
  ⟨p4Q2PZ35A_pauliQ1,
    p4Q2PZ35B_pauliQ1_mem_SU2⟩

/-- Genuine SU(2) quaternion K, with matrix exactly the PZ35A K. -/
def p4Q2PZ35B_quaternionK : G :=
  ⟨p4Q2PZ35A_pauliQ2,
    p4Q2PZ35B_pauliQ2_mem_SU2⟩

/-- The third quaternion L is the product J*K IN THE ORIGINAL SU(2). -/
def p4Q2PZ35B_quaternionL : G :=
  p4Q2PZ35B_quaternionJ * p4Q2PZ35B_quaternionK

/-- The quaternion product has the exact PZ35A L matrix. -/
theorem p4Q2PZ35B_quaternionL_coe :
    ((p4Q2PZ35B_quaternionL : G) : Mat) =
      p4Q2PZ35A_pauliQ3 := by
  change p4Q2PZ35A_pauliQ1 * p4Q2PZ35A_pauliQ2 =
    p4Q2PZ35A_pauliQ3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p4Q2PZ35A_pauliQ1, p4Q2PZ35A_pauliQ2,
      p4Q2PZ35A_pauliQ3]

/-- All four fixed twirl points are literal elements of the original SU(2). -/
def p4Q2PZ35B_quaternionFamily : Fin 4 → G :=
  ![(1 : G), p4Q2PZ35B_quaternionJ,
    p4Q2PZ35B_quaternionK, p4Q2PZ35B_quaternionL]

@[simp] theorem p4Q2PZ35B_quaternionFamily_zero :
    p4Q2PZ35B_quaternionFamily 0 = (1 : G) := rfl

@[simp] theorem p4Q2PZ35B_quaternionFamily_one :
    p4Q2PZ35B_quaternionFamily 1 = p4Q2PZ35B_quaternionJ := rfl

@[simp] theorem p4Q2PZ35B_quaternionFamily_two :
    p4Q2PZ35B_quaternionFamily 2 = p4Q2PZ35B_quaternionK := rfl

@[simp] theorem p4Q2PZ35B_quaternionFamily_three :
    p4Q2PZ35B_quaternionFamily 3 = p4Q2PZ35B_quaternionL := rfl

/-- Matrix coordinates of all four genuinely special-unitary twirl points. -/
theorem p4Q2PZ35B_quaternionFamily_coe (k : Fin 4) :
    ((p4Q2PZ35B_quaternionFamily k : G) : Mat) =
      ![p4Q2PZ35A_pauliQ0, p4Q2PZ35A_pauliQ1,
        p4Q2PZ35A_pauliQ2, p4Q2PZ35A_pauliQ3] k := by
  fin_cases k
  · change (1 : Mat) = p4Q2PZ35A_pauliQ0
    ext i j
    fin_cases i <;> fin_cases j <;> simp [p4Q2PZ35A_pauliQ0]
  · rfl
  · rfl
  · exact p4Q2PZ35B_quaternionL_coe

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35B_pauliQ1_mem_SU2
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35B_pauliQ2_mem_SU2
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35B_quaternionL_coe
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35B_quaternionFamily_coe
